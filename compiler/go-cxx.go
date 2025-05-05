package main

import (
	_ "embed"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"

	core "github.com/jurgen-kluft/go-cxx/core"

	"golang.org/x/tools/go/packages"
)

const lineWithSpaces = "                                                                                                     "

type TextStream struct {
	Indent         int
	IndentInSpaces int
	BlockEnded     bool
	Line           string
	Lines          []string
}

func newTextStream(reserveLines int) *TextStream {
	return &TextStream{
		Indent:         0,
		IndentInSpaces: 4,
		BlockEnded:     false,
		Line:           "",
		Lines:          make([]string, 0, reserveLines),
	}
}

func (ts *TextStream) blockStart() {
	ts.Indent++
}

func (ts *TextStream) blockEnd() {
	ts.Indent--
	if ts.Indent < 0 {
		ts.Indent = 0
	}
	ts.BlockEnded = true
}

func (ts *TextStream) flush() {
	if len(ts.Line) > 0 {
		ts.Lines = append(ts.Lines, ts.Line)
		ts.Line = ""
	}
}

func (ts *TextStream) write(s string) {
	if len(ts.Line) == 0 {
		numSpaces := ts.Indent * ts.IndentInSpaces
		ts.Line = lineWithSpaces[0:numSpaces] + s
	} else {
		ts.Line += s
	}
}

func (ts *TextStream) writeLn(lines ...string) {
	if len(ts.Line) == 0 {
		if len(lines) == 0 {
			ts.Lines = append(ts.Lines, "")
		} else {
			numSpaces := ts.Indent * ts.IndentInSpaces
			for _, line := range lines {
				ts.Lines = append(ts.Lines, lineWithSpaces[0:numSpaces]+line)
			}
		}
		return
	}

	if len(lines) > 0 {
		ts.Line += lines[0]
		ts.Lines = append(ts.Lines, ts.Line)
		ts.Line = ""
		for i := 1; i < len(lines); i++ {
			numSpaces := ts.Indent * ts.IndentInSpaces
			ts.Lines = append(ts.Lines, lineWithSpaces[0:numSpaces]+lines[i])
		}
	} else if len(lines) == 0 {
		ts.Lines = append(ts.Lines, ts.Line)
		ts.Line = ""
	}
}

func (ts *TextStream) string() string {
	if len(ts.Line) > 0 {
		ts.Lines = append(ts.Lines, ts.Line)
	}
	return strings.Join(ts.Lines, "\n")
}

// Go Package
//    {Go file}
//        Imports (can become C++ include statements)
//        Structs
//        - Fields, public and private
//        - Methods, public and private
//        - TODO: interfaces (C++ abstract classes, inheritance)
//        - TODO: things like Print(var_args ...any)
//        Global/Private Functions
//        Global/Private Variables
//        Global/Private Constants
//        Public/Private Function Pointers

// Supported Types
// - All primitive types, integers, unsigned integers, floats, strings
// - Array
// - Map

type FunctionInfo struct {
	Public     bool
	Const      bool
	Method     bool
	Name       string
	ReturnType string
	ParamNames []string
	ParamTypes []string
	Body       *ast.BlockStmt
}

func newFunctionInfo(public bool, mutating bool, method bool, name string) *FunctionInfo {
	return &FunctionInfo{
		Public:     public,
		Const:      !mutating,
		Method:     method,
		Name:       name,
		ReturnType: "void",
		ParamNames: make([]string, 0),
		ParamTypes: make([]string, 0),
		Body:       nil,
	}
}

func (fn FunctionInfo) writeDecl(text *TextStream) {
	text.write(fn.ReturnType)
	text.write(" ")
	text.write(fn.Name)
	text.write("(")
	for i, nParams := 0, len(fn.ParamNames); i < nParams; i++ {
		if i > 0 {
			text.write(", ")
		}
		text.write(fn.ParamTypes[i])
		text.write(" ")
		text.write(fn.ParamNames[i])
	}
	if fn.Const && fn.Method {
		text.writeLn(") const;")
	} else {
		text.writeLn(");")
	}
}

func (fn FunctionInfo) writeImpl(text *TextStream, cl *Compiler) {
	text.write(fn.ReturnType)
	text.write(" ")
	text.write(fn.Name)
	text.write("(")
	for i, nParams := 0, len(fn.ParamNames); i < nParams; i++ {
		if i > 0 {
			text.write(", ")
		}
		text.write(fn.ParamTypes[i])
		text.write(" ")
		text.write(fn.ParamNames[i])
	}
	text.writeLn(")")

	if fn.Body != nil {
		cl.writeBlockStmt(fn.Body, text)
	}
}

type FunctionPtrInfo struct {
	Public     bool
	Name       string
	ReturnType string
	ParamNames []string
	ParamTypes []string
}

func newFunctionPtrInfo(public bool, name string) *FunctionPtrInfo {
	return &FunctionPtrInfo{
		Public:     public,
		Name:       name,
		ReturnType: "void",
		ParamNames: make([]string, 0),
		ParamTypes: make([]string, 0),
	}
}

type MemberInfo struct {
	Public bool
	Const  bool
	Name   string
	Type   string
	Value  []string // default value
}

func newMemberInfo(name string, typ string, value []string) *MemberInfo {
	return &MemberInfo{
		Public: true,
		Name:   name,
		Type:   strings.TrimSpace(typ),
		Value:  value,
	}
}

func (m MemberInfo) writeDecl(text *TextStream) {
	if m.Const {
		text.write("const ")
	}
	text.write(m.Type)
	text.write(" ")
	text.write(m.Name)
	if len(m.Value) > 0 {
		text.write(" = ")
		for i, l := range m.Value {
			if i > 0 {
				text.writeLn()
			}
			text.write(l)
		}
	}
	text.writeLn(";")
}

type StructInfo struct {
	Name    string
	Public  bool
	Methods map[string]*FunctionInfo
	Members map[string]*MemberInfo
}

func newStructInfo(name string, public bool) *StructInfo {
	return &StructInfo{
		Name:    name,
		Public:  public,
		Methods: make(map[string]*FunctionInfo),
		Members: make(map[string]*MemberInfo),
	}
}

func (s *StructInfo) writeDecl(text *TextStream) {
	text.write("struct ")
	text.writeLn(s.Name)
	text.writeLn("{")

	text.blockStart()

	// Public methods
	numPrivateMethods := 0
	for _, method := range s.Methods {
		if method.Public {
			method.writeDecl(text)
		} else {
			numPrivateMethods++
		}
	}

	// Public members
	numPrivateMembers := 0
	for _, member := range s.Members {
		if member.Public {
			member.writeDecl(text)
		} else {
			numPrivateMembers++
		}
	}

	if numPrivateMembers > 0 || numPrivateMethods > 0 {
		text.blockEnd()
		text.writeLn("private:")
		text.blockStart()

		// Private methods
		for _, method := range s.Methods {
			if !method.Public {
				method.writeDecl(text)
			}
		}

		// Private members
		for _, member := range s.Members {
			if !member.Public {
				member.writeDecl(text)
			}
		}
	}

	text.blockEnd()
	text.writeLn("};")
	text.writeLn()
}

func (s *StructInfo) writeMethodImplementations(text *TextStream, cl *Compiler) {
	// Public methods
	for _, method := range s.Methods {
		text.write(method.ReturnType)
		text.write(" ")
		text.write(s.Name)
		text.write("::")
		text.write(method.Name)

		delimiter := ""
		text.write("(")
		for i, nParams := 0, len(method.ParamNames); i < nParams; i++ {
			text.write(delimiter)
			text.write(method.ParamTypes[i])
			text.write(" ")
			text.write(method.ParamNames[i])
			delimiter = ", "
		}
		if method.Const {
			text.writeLn(") const")
		} else {
			text.writeLn(")")
		}

		if method.Body != nil {
			cl.writeBlockStmt(method.Body, text)
		} else {
			text.writeLn("{")
			text.blockStart()
			text.writeLn("// TODO: Not implemented!")
			text.blockEnd()
			text.writeLn("}")
		}
	}
}

type GoFile struct {
	name     string
	settings *core.Settings

	cppSource *TextStream
	cppHeader *TextStream
	includes  []string

	vars      map[string]*MemberInfo
	funcPtrs  map[string]*FunctionPtrInfo
	functions map[string]*FunctionInfo
	structs   map[string]*StructInfo

	typeSpecs  []*ast.TypeSpec
	valueSpecs []*ast.ValueSpec
	funcDecls  []*ast.FuncDecl

	objTypeSpecs  map[types.Object]*ast.TypeSpec
	objValueSpecs map[types.Object]*ast.ValueSpec
	objFuncDecls  map[types.Object]*ast.FuncDecl
}

func (gf *GoFile) getIncludeGuardIdentifier() string {
	id := strings.ToUpper(gf.name)
	id = strings.ReplaceAll(id, "/", "_")
	return "__GO_CXX_" + id + "_GENERATED__"

}

func (gf *GoFile) registerInclude(include string) {
	if slices.Contains(gf.includes, include) {
		return
	}
	gf.includes = append(gf.includes, include)
}

// mapInsert is a helper function to insert a key-value pair into a map, and return
// whether the key was already present in the map. It returns false if the key was
// already present and thus not inserted, and true if it was inserted.
func mapInsert[Map ~map[K]V, K comparable, V any](m Map, key K, value V) (ok bool) {
	if _, ok = m[key]; !ok {
		m[key] = value
	}
	return !ok
}

func (gf *GoFile) writeIncludes(text *TextStream) {
	includeGuard := map[string]bool{} // Do not include the same file multiple times

	for _, include := range gf.settings.Includes {
		if mapInsert(includeGuard, include, true) {
			text.writeLn("#include \"" + include + "\"")
		}
	}
	for _, include := range gf.includes {
		if mapInsert(includeGuard, include, true) {
			text.writeLn("#include \"" + include + "\"")
		}
	}
}

func (gf *GoFile) hasPublicVars() bool {
	for _, member := range gf.vars {
		if member.Public {
			return true
		}
	}
	return false
}

func (gf *GoFile) hasPrivateVars() bool {
	for _, member := range gf.vars {
		if !member.Public {
			return true
		}
	}
	return false
}

func (gf *GoFile) hasPublicStructs() bool {
	for _, structInfo := range gf.structs {
		if structInfo.Public {
			return true
		}
	}
	return false
}

func (gf *GoFile) hasPrivateStructs() bool {
	for _, structInfo := range gf.structs {
		if !structInfo.Public {
			return true
		}
	}
	return false
}

type GoPackage struct {
	name     string
	pkg      *packages.Package
	settings *core.Settings
	types    *types.Info
	goFiles  map[string]*GoFile
}

func newGoPackage(pkg *packages.Package, settings *core.Settings) *GoPackage {
	return &GoPackage{
		name:     pkg.Types.Name(),
		pkg:      pkg,
		settings: settings,
		types:    pkg.TypesInfo,
		goFiles:  make(map[string]*GoFile),
	}
}

func (gp *GoPackage) newGoFile(filename string) *GoFile {
	if goFile, ok := gp.goFiles[filename]; ok {
		return goFile
	}

	goFile := &GoFile{
		name:          filename,
		settings:      gp.settings, // default behavior; a GoFile inherits the settings of the GoPackage
		cppSource:     nil,
		cppHeader:     nil,
		includes:      make([]string, 0),
		vars:          make(map[string]*MemberInfo),
		funcPtrs:      make(map[string]*FunctionPtrInfo),
		functions:     make(map[string]*FunctionInfo),
		structs:       make(map[string]*StructInfo),
		typeSpecs:     make([]*ast.TypeSpec, 0),
		valueSpecs:    make([]*ast.ValueSpec, 0),
		funcDecls:     make([]*ast.FuncDecl, 0),
		objTypeSpecs:  make(map[types.Object]*ast.TypeSpec),
		objValueSpecs: make(map[types.Object]*ast.ValueSpec),
		objFuncDecls:  make(map[types.Object]*ast.FuncDecl),
	}
	gp.goFiles[filename] = goFile
	return goFile
}

type Compiler struct {
	mainPkgPath     string
	outputPrefix    string
	currentGoPkg    *GoPackage
	currentGoFile   *GoFile
	fileSet         *token.FileSet
	cppTypes        map[types.BasicKind]string
	nameToGoPackage map[string]*GoPackage
	fieldIndices    map[*types.Var]int
	methodRenames   map[types.Object]string
	methodFieldTags map[types.Object]string
	genTypeExprs    map[types.Type]string
	genTypeDecls    map[*ast.TypeSpec]string
	genTypeDefns    map[*ast.TypeSpec]string
	genTypeMetas    map[*ast.TypeSpec]string
	genFuncDecls    map[*ast.FuncDecl]string

	genIdentifierCount int

	errors *strings.Builder
}

func newCompiler(mainPkgPath string) *Compiler {
	return &Compiler{
		mainPkgPath:  mainPkgPath,
		outputPrefix: "__",
		cppTypes: map[types.BasicKind]string{
			types.Bool:         "bool",
			types.UntypedBool:  "bool",
			types.Float32:      "float",
			types.UntypedFloat: "float",
			types.Float64:      "double",
			types.Int:          "int",
			types.UntypedInt:   "int",
			types.Int8:         "int8_t",
			types.Int16:        "int16_t",
			types.Int32:        "int32_t",
			types.Int64:        "int64_t",
			types.Uint:         "unsigned int",
			types.Uint8:        "uint8_t",
			types.Uint16:       "uint16_t",
			types.Uint32:       "uint32_t",
			types.Uint64:       "uint64_t",
			types.String:       "string",
		},
		nameToGoPackage:    make(map[string]*GoPackage),
		fieldIndices:       make(map[*types.Var]int),
		methodRenames:      make(map[types.Object]string),
		methodFieldTags:    make(map[types.Object]string),
		genTypeExprs:       make(map[types.Type]string),
		genTypeDecls:       make(map[*ast.TypeSpec]string),
		genTypeDefns:       make(map[*ast.TypeSpec]string),
		genTypeMetas:       make(map[*ast.TypeSpec]string),
		genFuncDecls:       make(map[*ast.FuncDecl]string),
		genIdentifierCount: 0,
		errors:             new(strings.Builder),
	}
}

// Types:      map[ast.Expr]types.TypeAndValue{},
// Instances:  map[*ast.Ident]types.Instance{},
// Defs:       map[*ast.Ident]types.Object{},
// Uses:       map[*ast.Ident]types.Object{},
// Implicits:  map[ast.Node]types.Object{},
// Selections: map[*ast.SelectorExpr]*types.Selection{},
// Scopes:     map[ast.Node]*types.Scope{},

// We go through the Compiler to find any of the above maps.

// TypeOf returns the type of expression e, or nil if not found.
// Precondition: the Types, Uses and Defs maps are populated.
func (cl *Compiler) typesTypeOf(e ast.Expr) (string, types.Type) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		t := pkgCtx.types.TypeOf(e)
		if t != nil {
			return pkgId, t
		}
	}
	return "unknown", nil
}

func (cl *Compiler) typesInstanceOf(id *ast.Ident) (string, types.Instance) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		if inst, ok := pkgCtx.types.Instances[id]; ok {
			return pkgId, inst
		}
	}
	return "unknown", types.Instance{}
}

func (cl *Compiler) typesObjectOf(id *ast.Ident) (string, types.Object) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		obj := pkgCtx.types.ObjectOf(id)
		if obj != nil {
			return pkgId, obj
		}
	}
	return "unknown", nil
}

func (cl *Compiler) typesDef(ident *ast.Ident) (string, types.Object) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		obj := pkgCtx.types.Defs[ident]
		if obj != nil {
			return pkgId, obj
		}
	}
	return "unknown", nil
}

func (cl *Compiler) typesTypes(ident *ast.Ident) (string, types.TypeAndValue) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		if t, ok := pkgCtx.types.Types[ident]; ok {
			return pkgId, t
		}
	}
	return "unknown", types.TypeAndValue{}
}

func (cl *Compiler) typesTypesFromExp(ident ast.Expr) (string, types.TypeAndValue) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		if t, ok := pkgCtx.types.Types[ident]; ok {
			return pkgId, t
		}
	}
	return "unknown", types.TypeAndValue{}
}

func (cl *Compiler) typesUses(ident *ast.Ident) (string, types.Object) {
	for pkgId, pkgCtx := range cl.nameToGoPackage {
		obj := pkgCtx.types.Uses[ident]
		if obj != nil {
			return pkgId, obj
		}
	}
	return "unknown", nil
}

func (cl *Compiler) getFullyQualifiedName(typ types.Type) string {
	// Include the package name in the type name if it is not the current package
	fullyQualifiedName := types.TypeString(typ, QualifierNameOf)
	packageAndType := strings.Split(fullyQualifiedName, ".")
	packageName := packageAndType[0]
	typeName := packageAndType[1]

	// The package name needs to be substituted with the namespace and/or instance specifier
	if goPkg, ok := cl.nameToGoPackage[packageName]; ok {
		if goPkg != cl.currentGoPkg {
			if goPkg.settings.Namespace != "" {
				return goPkg.settings.Namespace + "::" + typeName
			}
			if goPkg.settings.Instance != "" {
				return goPkg.settings.Instance + "." + typeName
			}
		}
	}
	return typeName

}

//
// Error and writing utilities
//

func (cl *Compiler) errorf(pos token.Pos, format string, args ...interface{}) {
	fmt.Fprintf(cl.errors, "%s: ", cl.fileSet.PositionFor(pos, true))
	fmt.Fprintf(cl.errors, format, args...)
	fmt.Fprintln(cl.errors)
}

func (cl *Compiler) errored() bool {
	return cl.errors.Len() != 0
}

func trimFinalSpace(s string) string {
	if l := len(s); l > 0 && s[l-1] == ' ' {
		return s[0 : l-1]
	} else {
		return s
	}
}

func (cl *Compiler) generateIdentifier(prefix string) string {
	cl.genIdentifierCount++
	builder := &strings.Builder{}
	builder.WriteString("gx__")
	builder.WriteString(prefix)
	builder.WriteString(strconv.Itoa(cl.genIdentifierCount))
	return builder.String()
}

//
// Types
//

func (cl *Compiler) getSignatureReturnType(sig *types.Signature) (types.Type, error) {
	if sig == nil || sig.Results() == nil {
		return nil, fmt.Errorf("signature is nil")
	}
	if sig.Results().Len() == 1 {
		t := sig.Results().At(0).Type()
		return t, nil
	}
	if sig.Results().Len() > 1 {
		t := sig.Results().At(0).Type()
		return t, fmt.Errorf("multiple return values not supported")
	}
	return nil, nil
}

// genTypeExpr generates a C++ type expression for the given Go type.
// Example: int -> int, *int -> int*, []int -> std::vector<int>
func (cl *Compiler) genTypeExpr(typ types.Type, pos token.Pos, varName string) string {
	// if result, ok := cl.genTypeExprs[typ]; ok {
	// 	return result
	// }

	builder := &strings.Builder{}
	switch typ := typ.(type) {
	case *types.Basic:
		if ts, ok := cl.cppTypes[typ.Kind()]; ok {
			builder.WriteString(ts)
		} else {
			cl.errorf(pos, "%s not supported", typ.String())
		}
		builder.WriteByte(' ')
	case *types.Pointer:
		if typ, ok := typ.Elem().(*types.Basic); ok && typ.Kind() == types.String {
			builder.WriteString("const ")
		}
		builder.WriteString(cl.genTypeExpr(typ.Elem(), pos, varName))
		builder.WriteByte('*')
	case *types.Named:
		fullyQualifiedName := cl.getFullyQualifiedName(typ)
		builder.WriteString(fullyQualifiedName)

		if typeArgs := typ.TypeArgs(); typeArgs != nil {
			builder.WriteString("<")
			for i, nTypeArgs := 0, typeArgs.Len(); i < nTypeArgs; i++ {
				if i > 0 {
					builder.WriteString(", ")
				}
				builder.WriteString(trimFinalSpace(cl.genTypeExpr(typeArgs.At(i), pos, varName)))
			}
			builder.WriteString(">")
		}
		builder.WriteByte(' ')
	case *types.TypeParam:
		// TODO: namespace ?
		builder.WriteString(typ.Obj().Name())
		builder.WriteByte(' ')
	case *types.Array:
		builder.WriteString("gx::Array<")
		builder.WriteString(trimFinalSpace(cl.genTypeExpr(typ.Elem(), pos, varName)))
		builder.WriteString(", ")
		builder.WriteString(strconv.FormatInt(typ.Len(), 10))
		builder.WriteString(">")
		builder.WriteByte(' ')
	case *types.Slice:
		builder.WriteString("gx::Slice<")
		builder.WriteString(trimFinalSpace(cl.genTypeExpr(typ.Elem(), pos, varName)))
		builder.WriteString(">")
		builder.WriteByte(' ')
	case *types.Signature:
		// C++ Function Pointer
		// Example: typedef int (*FuncType)(int, int);
		// This should return FuncType
		builder.WriteString(varName)
	default:
		cl.errorf(pos, "%s not supported", typ.String())
	}

	result := builder.String()
	cl.genTypeExprs[typ] = result
	return result
}

func (cl *Compiler) genTypeDecl(typeSpec *ast.TypeSpec) string {
	if result, ok := cl.genTypeDecls[typeSpec]; ok {
		return result
	}

	builder := &strings.Builder{}
	if typeSpec.TypeParams != nil {
		builder.WriteString("template<")
		for i, typeParam := range typeSpec.TypeParams.List {
			for j, name := range typeParam.Names {
				if i > 0 || j > 0 {
					builder.WriteString(", ")
				}
				builder.WriteString("typename ")
				builder.WriteString(name.String())
			}
		}
		builder.WriteString(">\n")
	}
	switch typeSpec.Type.(type) {
	case *ast.StructType:
		builder.WriteString("struct ")
		builder.WriteString(typeSpec.Name.String())
	case *ast.InterfaceType:
		// Empty -- only used as generic constraint during typecheck
		builder = &strings.Builder{}
	case *ast.FuncType:
		// C++ Function Pointer
		// Example: typedef int (*FuncType)(int, int);
		builder.WriteString("typedef ")
		_, typ := cl.typesTypeOf(typeSpec.Type)

		// Return type
		// TODO what if the return type is a struct type, we need a fully qualified name
		returnType, _ := cl.getSignatureReturnType(typ.(*types.Signature))
		builder.WriteString(returnType.String())
		builder.WriteString(" (*")
		builder.WriteString(typeSpec.Name.String())
		builder.WriteString(")(")
		if sig, ok := typ.(*types.Signature); ok {
			for i, nParams := 0, sig.Params().Len(); i < nParams; i++ {
				if i > 0 {
					builder.WriteString(", ")
				}
				param := sig.Params().At(i)
				builder.WriteString(cl.genTypeExpr(param.Type(), param.Pos(), ""))
				builder.WriteString(param.Name())
			}
		}
		builder.WriteString(")")

	default:
		builder.WriteString("using ")
		builder.WriteString(typeSpec.Name.String())
		builder.WriteString(" = ")
		_, typ := cl.typesTypeOf(typeSpec.Type)
		builder.WriteString(trimFinalSpace(cl.genTypeExpr(typ, typeSpec.Type.Pos(), "")))
	}

	result := builder.String()
	cl.genTypeDecls[typeSpec] = result
	return result
}

func QualifierNameOf(pkg *types.Package) string {
	if pkg == nil {
		return ""
	}
	return pkg.Name()
}

func QualifierNameOfExcept(except *types.Package) types.Qualifier {
	return func(p *types.Package) string {
		if p == except {
			return ""
		}
		return p.Name()
	}
}

// genTypeDefn generates a C++ type definition for the given Go type.
// Example: type S struct { a int; b string } -> struct S { int a; gx::String b }
// Example: type S func(int, int) -> typedef int (*S)(int, int);
// Example: type S *int -> using S = int*
func (cl *Compiler) genTypeDefn(typeSpec *ast.TypeSpec) {
	switch typ := typeSpec.Type.(type) {
	case *ast.StructType:
		// Create StructInfo and parse the fields
		//pkgCtx := cl.currentGoPkg
		fileCtx := cl.currentGoFile
		{
			structName := typeSpec.Name.String()
			structInfo, ok := fileCtx.structs[structName]
			if !ok {
				structPublic := typeSpec.Name.IsExported()
				structInfo = newStructInfo(structName, structPublic)
				fileCtx.structs[structName] = structInfo
			}

			// Parse the struct members
			for _, field := range typ.Fields.List {
				if _, fieldType := cl.typesTypeOf(field.Type); fieldType != nil {
					var defaultVal []string
					if tag := field.Tag; tag != nil && tag.Kind == token.STRING {
						unquoted, _ := strconv.Unquote(tag.Value)
						tagValue := reflect.StructTag(unquoted).Get("default")
						defaultVal = append(defaultVal, strings.Split(tagValue, "\n")...)
					}

					typeExpr := cl.genTypeExpr(fieldType, field.Type.Pos(), "")
					for _, fieldName := range field.Names {
						member := newMemberInfo(fieldName.String(), typeExpr, defaultVal)
						member.Public = fieldName.IsExported()
						member.Value = defaultVal
						structInfo.Members[member.Name] = member
					}
				}
			}
		}
	case *ast.InterfaceType:
		// Empty -- only used as generic constraint during typecheck
	default:
		// Empty -- alias declaration is definition
	}
}

//
// Functions
//

var methodFieldTagRe = regexp.MustCompile(`^(.*)_([^_]*)$`)

// genFuncDecl generates a C++ function declaration for the given Go function declaration.
// Example: func f(a int, b string) -> void f(int a, const gx::String &b)
func (cl *Compiler) genFuncDecl(decl *ast.FuncDecl) string {
	if result, ok := cl.genFuncDecls[decl]; ok {
		return result
	}

	// TODO Do we need the package Id that is returned here ?
	_, obj := cl.typesDef(decl.Name)
	sig := obj.Type().(*types.Signature)
	recv := sig.Recv()

	builder := &strings.Builder{}

	// Template types, type parameters
	addTypeParams := func(typeParams *types.TypeParamList) {
		if typeParams != nil {
			builder.WriteString("template<")
			for i, nTypeParams := 0, typeParams.Len(); i < nTypeParams; i++ {
				if i > 0 {
					builder.WriteString(", ")
				}
				builder.WriteString("typename ")
				builder.WriteString(typeParams.At(i).Obj().Name())
			}
			builder.WriteString(">\n")
		}
	}

	var recvNamedType *types.Named
	funcIsMutating := false
	if recv != nil {
		switch recvType := recv.Type().(type) {
		case *types.Named:
			recvNamedType = recvType
			addTypeParams(recvType.TypeParams())
		case *types.Pointer:
			funcIsMutating = true
			switch elemType := recvType.Elem().(type) {
			case *types.Named:
				recvNamedType = elemType
				addTypeParams(elemType.TypeParams())
			}
		}
	}
	addTypeParams(sig.TypeParams())

	// Return type
	if rets := sig.Results(); rets.Len() > 1 {
		cl.errorf(decl.Type.Results.Pos(), "multiple return values not supported")
	} else if rets.Len() == 1 {
		ret := rets.At(0)
		builder.WriteString(cl.genTypeExpr(ret.Type(), ret.Pos(), ""))
	} else {
		if obj.Pkg().Name() == "main" && decl.Name.String() == "main" && recv == nil {
			builder.WriteString("int ")
		} else {
			builder.WriteString("void ")
		}
	}

	// Field tag
	funcName := decl.Name.String()

	if recvNamedType != nil {
		if _, ok := recvNamedType.Underlying().(*types.Struct); ok {
			structName := recvNamedType.Obj().Name()
			structPublic := recvNamedType.Obj().Exported()
			funcPublic := decl.Name.IsExported()

			structInfo := cl.currentGoFile.structs[structName]
			if structInfo == nil {
				structInfo = newStructInfo(structName, structPublic)
				cl.currentGoFile.structs[structName] = structInfo
			}

			if _, ok := structInfo.Methods[funcName]; !ok {
				// In Go a method can be defined on a pointer or a value
				// receiver. In C++ we can make this function const if the
				// receiver is a value receiver.
				funcInfo := newFunctionInfo(funcPublic, funcIsMutating, true, funcName)
				if sig.Results() != nil && sig.Results().Len() == 1 {
					// Get the full return type as was used in the source code
					// e.g. func Name(a int) address.Address {}
					// So we need to get the 'address.Address' part

					// funcInfo.ReturnType = cl.genTypeExpr(sig.Results().At(0).Type(), decl.Type.Results.Pos(), "")

					// Get the return type from the signature
					// This results in 'Address'
					funcInfo.ReturnType = cl.genTypeExpr(sig.Results().At(0).Type(), decl.Type.Results.Pos(), "")
					funcInfo.ReturnType = strings.TrimSpace(funcInfo.ReturnType)

					// Now find the name of the package to prepend to the type

				}
				for i, nParams := 0, sig.Params().Len(); i < nParams; i++ {
					param := sig.Params().At(i)
					paramName := param.Name()
					paramType := cl.genTypeExpr(param.Type(), param.Pos(), "")
					paramType = strings.TrimSpace(paramType)
					funcInfo.ParamNames = append(funcInfo.ParamNames, paramName)
					funcInfo.ParamTypes = append(funcInfo.ParamTypes, paramType)
				}

				funcInfo.Body = decl.Body
				structInfo.Methods[funcInfo.Name] = funcInfo
			}
		}
	} else {
		// A standalone function
		funcInfo := cl.currentGoFile.functions[funcName]
		if funcInfo == nil {
			funcInfo = newFunctionInfo(decl.Name.IsExported(), false, false, funcName)
			funcInfo.Body = decl.Body
			if sig.Results() != nil && sig.Results().Len() == 1 {
				funcInfo.ReturnType = cl.genTypeExpr(sig.Results().At(0).Type(), decl.Type.Results.Pos(), "")
			}
			for i, nParams := 0, sig.Params().Len(); i < nParams; i++ {
				param := sig.Params().At(i)
				funcInfo.ParamNames = append(funcInfo.ParamNames, param.Name())
				funcInfo.ParamTypes = append(funcInfo.ParamTypes, cl.genTypeExpr(param.Type(), param.Pos(), ""))
			}
			cl.currentGoFile.functions[funcName] = funcInfo
		}
	}

	// Name
	builder.WriteString(funcName)

	// Parameters
	builder.WriteByte('(')
	addParam := func(param *types.Var) {
		typ := param.Type()
		if _, ok := typ.(*types.Signature); ok {
			builder.WriteString("auto &&")
		} else if basicType, ok := typ.(*types.Basic); ok && basicType.Kind() == types.String {
			builder.WriteString("const gx::String &")
		} else {
			builder.WriteString(cl.genTypeExpr(typ, param.Pos(), ""))
		}
		builder.WriteString(param.Name())
	}
	if recv != nil {
		// if fieldTag != "" {
		// 	builder.WriteString(fieldTag)
		// 	builder.WriteString(", ")
		// }
		addParam(recv)
	}
	for i, nParams := 0, sig.Params().Len(); i < nParams; i++ {
		if i > 0 || recv != nil {
			builder.WriteString(", ")
		}
		addParam(sig.Params().At(i))
	}
	builder.WriteByte(')')

	result := builder.String()
	cl.genFuncDecls[decl] = result
	return result
}

// ----------------------------------------------------------
// ----------------------------------------------------------
//                        Expressions
// ----------------------------------------------------------
// ----------------------------------------------------------

func (cl *Compiler) getIdent(ident *ast.Ident) string {
	_, typ := cl.typesTypes(ident)
	if typ.IsNil() {
		return "nullptr"
	}
	if typ.IsBuiltin() {
		return "gx::"
	}

	// if ext, ok := cl.namespace[cl.types.Uses[ident]]; ok {
	// 	return ext
	// }

	// TODO: Package namespace
	typName := types.TypeString(typ.Type, QualifierNameOf)
	fmt.Println(typName)

	return ident.Name
}

func (cl *Compiler) getBasicLit(lit *ast.BasicLit) string {
	switch lit.Kind {
	case token.INT:
		return (lit.Value)
	case token.FLOAT:
		return (lit.Value + "f")
	case token.STRING:
		if lit.Value[0] == '`' {
			return ("R\"(" + lit.Value[1:len(lit.Value)-1] + ")\"")
		}
		return (lit.Value)
	case token.CHAR:
		return (lit.Value)
	default:
		return ("unsupported literal kind")
	}
}

func (cl *Compiler) writeFuncLit(lit *ast.FuncLit, text *TextStream) {
	_, t := cl.typesTypeOf(lit)
	sig := t.(*types.Signature)
	if text.Indent == 0 {
		text.write("[](")
	} else {
		text.write("[&](")
	}
	for i, nParams := 0, sig.Params().Len(); i < nParams; i++ {
		if i > 0 {
			text.write(", ")
		}
		param := sig.Params().At(i)
		if _, ok := param.Type().(*types.Signature); ok {
			text.write("auto &&")
		} else if basicType, ok := param.Type().(*types.Basic); ok && basicType.Kind() == types.String {
			text.write("const gx::String &")
		} else {
			text.write(cl.genTypeExpr(param.Type(), param.Pos(), ""))
		}
		text.write(param.Name())
	}
	text.write(") ")

	text.blockStart()
	{
		cl.writeBlockStmt(lit.Body, text)
	}
	text.blockEnd()
}

func (cl *Compiler) writeCompositeLit(lit *ast.CompositeLit, text *TextStream) {
	useParens := true
	_, typeof := cl.typesTypeOf(lit)
	typeExpr := (cl.genTypeExpr(typeof, lit.Pos(), ""))
	if useParens {
		text.write(trimFinalSpace(typeExpr))
		text.write("(")
	} else {
		text.write(typeExpr)
		text.write("{")
	}
	if len(lit.Elts) > 0 {
		if _, ok := lit.Elts[0].(*ast.KeyValueExpr); ok {
			_, typeof = cl.typesTypeOf(lit)
			if typ, ok := typeof.Underlying().(*types.Struct); ok {
				// Fields
				if nFields := typ.NumFields(); nFields != 0 {
					if _, ok := cl.fieldIndices[typ.Field(0)]; !ok {
						for i := 0; i < nFields; i++ {
							cl.fieldIndices[typ.Field(i)] = i
						}
					}
				}

				// Methods

				// Check field order
				lastIndex := 0
				for _, elt := range lit.Elts {
					_, objof := cl.typesObjectOf(elt.(*ast.KeyValueExpr).Key.(*ast.Ident))
					field := objof.(*types.Var)

					if index := cl.fieldIndices[field]; index < lastIndex {
						cl.errorf(lit.Pos(), "struct literal fields must appear in definition order")
						break
					} else {
						lastIndex = index
					}
				}
			}
		}
		if cl.fileSet.Position(lit.Pos()).Line == cl.fileSet.Position(lit.Elts[0].Pos()).Line {
			if !useParens {
				text.write(" ")
			}
			for i, elt := range lit.Elts {
				if i > 0 {
					text.write(", ")
				}
				cl.writeExpr(elt, text)
			}
			if !useParens {
				text.write(" ")
			}
		} else {
			text.writeLn()
			text.blockStart()
			nElts := len(lit.Elts)
			for i, elt := range lit.Elts {
				cl.writeExpr(elt, text)
				if !(useParens && i == nElts-1) {
					text.write(",")
				}
				text.writeLn()
			}
			text.blockEnd()
		}
	}
	if useParens {
		text.write(")")
	} else {
		text.write("}")
	}
}

func (cl *Compiler) writeParenExpr(bin *ast.ParenExpr, text *TextStream) {
	text.write("(")
	cl.writeExpr(bin.X, text)
	text.write(")")
}

func (cl *Compiler) writeSelectorExpr(sel *ast.SelectorExpr, text *TextStream) {
	_, typeof := cl.typesTypeOf(sel.X)
	if basic, ok := typeof.(*types.Basic); !(ok && basic.Kind() == types.Invalid) {
		// TODO: do we really need this ?
		text.write("this->")
	}

	// Prefix with namespace and/or instance specifier
	if sel.X != nil {
		// pkgName := sel.X.(*ast.Ident).Name
		// scope := cl.getScope(pkgName)
		scope := cl.getScopeFromExpr(sel.X)
		identifier := cl.getIdent(sel.Sel)
		text.write(scope)
		text.write(identifier)
	} else {
		identifier := cl.getIdent(sel.Sel)
		text.write(identifier)
	}
}

func (cl *Compiler) getScopeFromExpr(expr ast.Expr) string {
	selector := ""
	switch expr := expr.(type) {
	case *ast.SelectorExpr:
		selector = expr.Sel.Name
	case *ast.Ident:
		selector = expr.Name
	default:
		return ""
	}

	if pkg, ok := cl.nameToGoPackage[selector]; ok {
		if pkg != cl.currentGoPkg {
			if pkg.settings.Namespace != "" {
				return pkg.settings.Namespace + "::"
			}
			if pkg.settings.Instance != "" {
				return pkg.settings.Instance + "."
			}
		}
	}
	return ""
}

func (cl *Compiler) writeIndexExpr(ind *ast.IndexExpr, text *TextStream) {
	_, typeof := cl.typesTypeOf(ind.X)
	if _, ok := typeof.(*types.Pointer); ok {
		text.write("gx::deref(")
		cl.writeExpr(ind.X, text)
		text.write(")")
	} else {
		cl.writeExpr(ind.X, text)
	}
	text.write("[")
	cl.writeExpr(ind.Index, text)
	text.write("]")
}

func (cl *Compiler) writeCallExpr(call *ast.CallExpr, text *TextStream) {
	method := false

	//funType := cl.types.Types[call.Fun]
	_, funType := cl.typesTypesFromExp(call.Fun)

	if _, ok := funType.Type.Underlying().(*types.Signature); ok || funType.IsBuiltin() {
		// Function or method
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
			_, obj := cl.typesUses(sel.Sel)
			if sig, ok := obj.Type().(*types.Signature); ok && sig.Recv() != nil {
				method = true
				if rename, ok := cl.methodRenames[obj]; ok {
					text.write(rename)
				} else {
					text.write(cl.getIdent(sel.Sel))
				}
				text.write("(")
				if fieldTag, ok := cl.methodFieldTags[obj]; ok {
					text.write(fieldTag)
					text.write("{}, ")
				}
				_, typeof := cl.typesTypeOf(sel.X)
				_, xPtr := typeof.(*types.Pointer)
				_, recvPtr := sig.Recv().Type().(*types.Pointer)
				if xPtr && !recvPtr {
					text.write("gx::deref(")
					cl.writeExpr(sel.X, text)
					text.write(")")
				} else if !xPtr && recvPtr {
					text.write("&(")
					cl.writeExpr(sel.X, text)
					text.write(")")
				} else {
					cl.writeExpr(sel.X, text)
				}
			}
		}
		if !method {
			var typeArgs *types.TypeList
			switch fun := call.Fun.(type) {
			case *ast.Ident: // f(...)
				text.write(cl.getIdent(fun))
				_, instance := cl.typesInstanceOf(fun)
				typeArgs = instance.TypeArgs
			case *ast.SelectorExpr: // pkg.f(...)
				// Prefix with namespace and/or instance specifier
				// if fun.Sel != nil {
				// 	pkgName := fun.X.(*ast.Ident).Name
				// 	text.write(cl.getScope(pkgName))
				// }
				scope := cl.getScopeFromExpr(fun.X)
				text.write(scope)
				text.write(cl.getIdent(fun.Sel))
				_, instance := cl.typesInstanceOf(fun.Sel)
				typeArgs = instance.TypeArgs
			case *ast.IndexExpr:
				switch fun := fun.X.(type) {
				case *ast.Ident: // f[T](...)
					text.write(cl.getIdent(fun))
					_, instance := cl.typesInstanceOf(fun)
					typeArgs = instance.TypeArgs
				case *ast.SelectorExpr: // pkg.f[T](...)
					text.write(cl.getIdent(fun.Sel))
					_, instance := cl.typesInstanceOf(fun.Sel)
					typeArgs = instance.TypeArgs
				}
			default:
				cl.writeExpr(fun, text)
			}

			if typeArgs != nil {
				text.write("<")
				for i, nTypeArgs := 0, typeArgs.Len(); i < nTypeArgs; i++ {
					if i > 0 {
						text.write(", ")
					}
					text.write(trimFinalSpace(cl.genTypeExpr(typeArgs.At(i), call.Fun.Pos(), "")))
				}
				text.write(">")
			}

			text.write("(")
		}
	} else {
		// Conversion
		typeExpr := trimFinalSpace(cl.genTypeExpr(funType.Type, call.Fun.Pos(), ""))
		if _, ok := call.Fun.(*ast.ParenExpr); ok {
			text.write("(")
			text.write(typeExpr)
			text.write(")")
		} else {
			text.write(typeExpr)
		}
		text.write("(")
	}
	for i, arg := range call.Args {
		if i > 0 || method {
			text.write(", ")
		}
		cl.writeExpr(arg, text)
	}
	text.write(")")
}

func (cl *Compiler) writeStarExpr(star *ast.StarExpr, text *TextStream) {
	text.write("gx::deref(")
	cl.writeExpr(star.X, text)
	text.write(")")
}

func (cl *Compiler) writeUnaryExpr(un *ast.UnaryExpr, text *TextStream) {
	switch op := un.Op; op {
	case token.ADD, token.SUB, token.NOT:
		text.write(op.String())
	case token.AND:
		_, t := cl.typesTypesFromExp(un.X)
		if !t.Addressable() {
			cl.errorf(un.OpPos, "cannot take address of a temporary object")
		}
		text.write(op.String())
	default:
		cl.errorf(un.OpPos, "unsupported unary operator")
	}
	cl.writeExpr(un.X, text)
}

func (cl *Compiler) writeBinaryExpr(bin *ast.BinaryExpr, text *TextStream) {
	needParens := false
	switch bin.Op {
	case token.AND, token.OR, token.XOR:
		needParens = true
	}
	if needParens {
		text.write("(")
	}
	cl.writeExpr(bin.X, text)
	text.write(" ")
	switch op := bin.Op; op {
	case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ,
		token.ADD, token.SUB, token.MUL, token.QUO, token.REM,
		token.AND, token.OR, token.XOR, token.SHL, token.SHR,
		token.LAND, token.LOR:
		text.write(op.String())
	default:
		cl.errorf(bin.OpPos, "unsupported binary operator")
	}
	text.write(" ")
	cl.writeExpr(bin.Y, text)
	if needParens {
		text.write(")")
	}
}

func (cl *Compiler) writeKeyValueExpr(kv *ast.KeyValueExpr, text *TextStream) {
	if name, ok := kv.Key.(*ast.Ident); !ok {
		cl.errorf(kv.Pos(), "unsupported literal key")
	} else {
		text.write(".")
		text.write(cl.getIdent(name))
		text.write(" = ")
		cl.writeExpr(kv.Value, text)
	}
}

func (cl *Compiler) writeExpr(expr ast.Expr, text *TextStream) {
	switch expr := expr.(type) {
	case *ast.Ident:
		text.write(cl.getIdent(expr))
	case *ast.BasicLit:
		text.write(cl.getBasicLit(expr))
	case *ast.FuncLit:
		cl.writeFuncLit(expr, text)
	case *ast.CompositeLit:
		cl.writeCompositeLit(expr, text)
	case *ast.ParenExpr:
		cl.writeParenExpr(expr, text)
	case *ast.SelectorExpr:
		cl.writeSelectorExpr(expr, text)
	case *ast.IndexExpr:
		cl.writeIndexExpr(expr, text)
	case *ast.CallExpr:
		cl.writeCallExpr(expr, text)
	case *ast.StarExpr:
		cl.writeStarExpr(expr, text)
	case *ast.UnaryExpr:
		cl.writeUnaryExpr(expr, text)
	case *ast.BinaryExpr:
		cl.writeBinaryExpr(expr, text)
	case *ast.KeyValueExpr:
		cl.writeKeyValueExpr(expr, text)
	default:
		cl.errorf(expr.Pos(), "unsupported expression type")
	}
}

//
// Statements
//

func (cl *Compiler) writeExprStmt(exprStmt *ast.ExprStmt, text *TextStream) {
	cl.writeExpr(exprStmt.X, text)
}

func (cl *Compiler) writeIncDecStmt(incDecStmt *ast.IncDecStmt, text *TextStream) {
	text.write("(")
	cl.writeExpr(incDecStmt.X, text)
	text.write(")")
	text.write(incDecStmt.Tok.String())
}

func (cl *Compiler) writeAssignStmt(assignStmt *ast.AssignStmt, text *TextStream) {
	if len(assignStmt.Lhs) != 1 {
		cl.errorf(assignStmt.Pos(), "multi-value assignment unsupported")
		return
	}
	if assignStmt.Tok == token.DEFINE {
		//typ := cl.types.TypeOf(assignStmt.Rhs[0])
		_, typ := cl.typesTypeOf(assignStmt.Rhs[0])
		if typ, ok := typ.(*types.Basic); ok && typ.Kind() == types.String {
			text.write("gx::String ")
		} else {
			text.write("auto ")
		}
	}
	cl.writeExpr(assignStmt.Lhs[0], text)
	text.write(" ")
	switch op := assignStmt.Tok; op {
	case token.DEFINE:
		text.write("=")
	case token.ASSIGN,
		token.ADD_ASSIGN, token.SUB_ASSIGN, token.MUL_ASSIGN, token.QUO_ASSIGN, token.REM_ASSIGN,
		token.AND_ASSIGN, token.OR_ASSIGN, token.XOR_ASSIGN, token.SHL_ASSIGN, token.SHR_ASSIGN:
		text.write(op.String())
	default:
		cl.errorf(assignStmt.TokPos, "unsupported assignment operator")
	}
	text.write(" ")
	cl.writeExpr(assignStmt.Rhs[0], text)
}

func (cl *Compiler) writeDeferStmt(deferStmt *ast.DeferStmt, text *TextStream) {
	text.write("gx::Defer ")
	text.write(cl.generateIdentifier("Defer"))
	text.write("([&](){")
	text.writeLn()
	text.blockStart()
	cl.writeCallExpr(deferStmt.Call, text)
	text.write(";")
	text.writeLn()
	text.blockEnd()
	text.write("});")
}

func (cl *Compiler) writeReturnStmt(retStmt *ast.ReturnStmt, text *TextStream) {
	if len(retStmt.Results) > 1 {
		cl.errorf(retStmt.Results[0].Pos(), "multiple return values not supported")
	} else if len(retStmt.Results) == 1 {
		text.write("return ")
		cl.writeExpr(retStmt.Results[0], text)
	} else {
		text.write("return")
	}
}

func (cl *Compiler) writeBranchStmt(branchStmt *ast.BranchStmt, text *TextStream) {
	switch tok := branchStmt.Tok; tok {
	case token.BREAK, token.CONTINUE:
		text.write(tok.String())
	default:
		cl.errorf(branchStmt.TokPos, "unsupported branch statement")
	}
}

func (cl *Compiler) writeBlockStmt(block *ast.BlockStmt, text *TextStream) {
	text.writeLn("{")
	text.blockStart()
	cl.writeStmtList(block.List, text)
	text.blockEnd()
	text.writeLn("}")
}

func (cl *Compiler) writeIfStmt(ifStmt *ast.IfStmt, text *TextStream) {
	text.write("if (")
	if ifStmt.Init != nil {
		cl.writeStmt(ifStmt.Init, text)
		text.write("; ")
	}
	cl.writeExpr(ifStmt.Cond, text)
	text.write(") ")
	cl.writeStmt(ifStmt.Body, text)
	if ifStmt.Else != nil {
		text.write(" else ")
		cl.writeStmt(ifStmt.Else, text)
	}
}

func (cl *Compiler) writeForStmt(forStmt *ast.ForStmt, text *TextStream) {
	text.write("for (")
	if forStmt.Init != nil {
		cl.writeStmt(forStmt.Init, text)
	}
	text.write("; ")
	if forStmt.Cond != nil {
		cl.writeExpr(forStmt.Cond, text)
	}
	text.write("; ")
	if forStmt.Post != nil {
		cl.writeStmt(forStmt.Post, text)
	}
	text.write(") ")
	cl.writeStmt(forStmt.Body, text)
}

func (cl *Compiler) writeRangeStmt(rangeStmt *ast.RangeStmt, text *TextStream) {
	if rangeStmt.Tok == token.ASSIGN {
		cl.errorf(rangeStmt.TokPos, "must use := in range statement")
	}
	var key *ast.Ident
	if rangeStmt.Key != nil {
		if ident, ok := rangeStmt.Key.(*ast.Ident); ok && ident.Name != "_" {
			key = ident
		}
	}
	text.write("for (")
	if key != nil {
		text.write("auto ")
		text.write(cl.getIdent(key))
		text.write(" = -1; ")
	}
	text.write("auto &")
	if rangeStmt.Value != nil {
		cl.writeExpr(rangeStmt.Value, text)
	} else {
		if ident, ok := rangeStmt.Value.(*ast.Ident); ok && ident.Name != "_" {
			text.write(cl.getIdent(ident))
		} else {
			text.write("_ [[maybe_unused]]")
		}
	}
	text.write(" : ")
	cl.writeExpr(rangeStmt.X, text)
	text.writeLn(") {")
	text.blockStart()
	if key != nil {
		text.write("++")
		text.write(cl.getIdent(key))
		text.writeLn(";")
	}
	cl.writeStmtList(rangeStmt.Body.List, text)
	text.blockEnd()
	text.write("}")
}

func (cl *Compiler) writeDeclStmt(declStmt *ast.DeclStmt, text *TextStream) {
	fmt.Println(declStmt)
	// switch decl := declStmt.Decl.(type) {
	// case *ast.GenDecl:
	// 	for _, spec := range decl.Specs {
	// 		switch spec := spec.(type) {
	// 		case *ast.TypeSpec:
	// 			typeDefn := cl.genTypeDefn(spec)
	// 			typeDefnIndented := &strings.Builder{}
	// 			for _, r := range typeDefn {
	// 				typeDefnIndented.WriteRune(r)
	// 				if r == '\n' {
	// 					for i := 0; i < 2*cl.indent; i++ {
	// 						typeDefnIndented.WriteByte(' ')
	// 					}
	// 				}
	// 			}
	// 			text.write(typeDefnIndented.String())
	// 		default:
	// 			cl.errorf(declStmt.Pos(), "unsupported declaration statement")
	// 		}
	// 	}
	// }
}

func (cl *Compiler) writeStmt(stmt ast.Stmt, text *TextStream) string {
	switch stmt := stmt.(type) {
	case *ast.ExprStmt:
		cl.writeExprStmt(stmt, text)
	case *ast.IncDecStmt:
		cl.writeIncDecStmt(stmt, text)
	case *ast.AssignStmt:
		cl.writeAssignStmt(stmt, text)
	case *ast.DeferStmt:
		cl.writeDeferStmt(stmt, text)
	case *ast.ReturnStmt:
		cl.writeReturnStmt(stmt, text)
	case *ast.BranchStmt:
		cl.writeBranchStmt(stmt, text)
	case *ast.BlockStmt:
		cl.writeBlockStmt(stmt, text)
	case *ast.IfStmt:
		cl.writeIfStmt(stmt, text)
	case *ast.ForStmt:
		cl.writeForStmt(stmt, text)
	case *ast.RangeStmt:
		cl.writeRangeStmt(stmt, text)
	case *ast.DeclStmt:
		cl.writeDeclStmt(stmt, text)
	default:
		cl.errorf(stmt.Pos(), "unsupported statement type")
	}
	return ""
}

func (cl *Compiler) writeStmtList(list []ast.Stmt, text *TextStream) {
	for _, stmt := range list {
		cl.writeStmt(stmt, text)
		text.write(";")
		text.writeLn()
	}
}

// ----------------------------------------------------------
// ----------------------------------------------------------
//                         Top-level
// ----------------------------------------------------------
// ----------------------------------------------------------

func parseCoreSettings(lit *ast.CompositeLit, settings *core.Settings) {
	for _, elt := range lit.Elts {
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			if key, ok := kv.Key.(*ast.Ident); ok {
				if key.Name == "ExportSource" {
					if val, ok := kv.Value.(*ast.Ident); ok {
						settings.ExportSource = val.Name == "true"
					} else if val, ok := kv.Value.(*ast.BasicLit); ok {
						if val.Kind == token.STRING {
							settings.ExportSource = val.Value == "true"
						}
					}
				} else if key.Name == "ExportHeader" {
					if val, ok := kv.Value.(*ast.Ident); ok {
						settings.ExportHeader = val.Name == "true"
					} else if val, ok := kv.Value.(*ast.BasicLit); ok {
						if val.Kind == token.STRING {
							settings.ExportHeader = val.Value == "true"
						}
					}
				} else if key.Name == "Instance" {
					if val, ok := kv.Value.(*ast.Ident); ok {
						settings.Instance, _ = strconv.Unquote(val.Name)
					} else if val, ok := kv.Value.(*ast.BasicLit); ok {
						if val.Kind == token.STRING {
							settings.Instance, _ = strconv.Unquote(val.Value)
						}
					}
				} else if key.Name == "Namespace" {
					if val, ok := kv.Value.(*ast.BasicLit); ok {
						if val.Kind == token.STRING {
							settings.Namespace, _ = strconv.Unquote(val.Value)
						}
					}
				} else if key.Name == "OutputPrefix" {
					if val, ok := kv.Value.(*ast.BasicLit); ok {
						if val.Kind == token.STRING {
							settings.OutputPrefix, _ = strconv.Unquote(val.Value)
						}
					}
				} else if key.Name == "Includes" {
					// Includes is a []string
					if val, ok := kv.Value.(*ast.CompositeLit); ok {
						for _, elt := range val.Elts {
							if key, ok := elt.(*ast.BasicLit); ok {
								if key.Kind == token.STRING {
									settings.Includes = append(settings.Includes, strings.Trim(key.Value, "\""))
								}
							}
						}
					}
				}
			}
		}
	}
}

func (cl *Compiler) collectPackageSettings(pkg *packages.Package) *core.Settings {
	settings := core.NewSettings()
	for _, file := range pkg.Syntax {
		for _, decl := range file.Decls {
			switch decl := decl.(type) {
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					switch spec := spec.(type) {
					case *ast.ValueSpec:
						for vi, name := range spec.Names {
							if name.Name == "__settings" {
								specValue := spec.Values[vi]
								switch valueType := specValue.(type) {
								case *ast.CompositeLit:
									parseCoreSettings(valueType, settings)
									return settings
								}
							}
						}
					}
				}
			}
		}
	}
	return settings
}

func (cl *Compiler) getFilename(file *ast.File, cwd string) string {
	fileName := cl.fileSet.Position(file.Pos()).Filename
	// Make relative to the current directory
	if strings.HasPrefix(fileName, cwd) {
		fileName = fileName[len(cwd)+1:]
	}
	// Remove the ".go" extension
	if strings.HasSuffix(fileName, ".go") {
		fileName = fileName[:len(fileName)-3]
	}
	return fileName
}

func (cl *Compiler) compile() bool {
	// Load main package
	packagesConfig := &packages.Config{
		Mode: packages.NeedImports | packages.NeedDeps |
			packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo,
	}
	// Get the parent of the current working directory
	currentDir, err := os.Getwd()
	if err != nil {
		fmt.Fprintln(cl.errors, err)
		return false
	}
	currentDir = filepath.Dir(currentDir)

	loadPkgs, err := packages.Load(packagesConfig, cl.mainPkgPath)
	if err != nil {
		fmt.Fprintln(cl.errors, err)
	}
	if len(loadPkgs) == 0 {
		return false
	}
	for _, pkg := range loadPkgs {
		for _, err := range pkg.Errors {
			if err.Pos != "" {
				fmt.Fprintf(cl.errors, "%s: %s\n", err.Pos, err.Msg)
			} else {
				fmt.Fprintln(cl.errors, err.Msg)
			}
		}
	}
	if cl.errored() {
		return false
	}
	cl.fileSet = loadPkgs[0].Fset

	// Collect packages in dependency order
	var pkgs []*packages.Package
	{
		visited := map[*packages.Package]bool{}
		var visit func(pkg *packages.Package)
		visit = func(pkg *packages.Package) {
			if !visited[pkg] {
				visited[pkg] = true
				for _, dep := range pkg.Imports {
					visit(dep)
				}
				pkgs = append(pkgs, pkg)
				if pkg.Fset != cl.fileSet {
					cl.errorf(0, "internal error: filesets differ")
				}
			}
		}
		for _, pkg := range loadPkgs {
			visit(pkg)
		}
	}
	sort.Slice(pkgs, func(i, j int) bool {
		return pkgs[i].ID < pkgs[j].ID
	})

	for _, pkg := range pkgs {
		settings := cl.collectPackageSettings(pkg)
		cl.currentGoPkg = newGoPackage(pkg, settings)
		cl.nameToGoPackage[cl.currentGoPkg.name] = cl.currentGoPkg
	}

	// Collect exports
	// exports := map[types.Object]bool{}

	// Collect top-level decls and exports in output order
	{
		for _, pkg := range pkgs {
			goPkg := cl.nameToGoPackage[pkg.Types.Name()]
			cl.currentGoPkg = goPkg
			fmt.Println("Package Scope: " + pkg.Name)
			for _, file := range pkg.Syntax {
				// Get the name of the go file
				goFileName := cl.getFilename(file, currentDir)
				goFile := goPkg.newGoFile(goFileName)
				for _, decl := range file.Decls {
					switch decl := decl.(type) {
					case *ast.GenDecl:
						for _, spec := range decl.Specs {
							switch spec := spec.(type) {
							case *ast.TypeSpec:
								_, def := cl.typesDef(spec.Name)
								goFile.objTypeSpecs[def] = spec
							case *ast.ValueSpec:
								for _, name := range spec.Names {
									_, def := cl.typesDef(name)
									goFile.objValueSpecs[def] = spec
								}
							}
						}
					case *ast.FuncDecl:
						_, def := cl.typesDef(decl.Name)
						goFile.objFuncDecls[def] = decl
					}
				}
			}
		}

		typeSpecVisited := map[*ast.TypeSpec]bool{}
		valueSpecVisited := map[*ast.ValueSpec]bool{}
		for _, pkg := range pkgs {
			cl.currentGoPkg = cl.nameToGoPackage[pkg.Types.Name()]
			goPkg := cl.currentGoPkg
			if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
				continue
			}

			for _, file := range pkg.Syntax {
				goFilename := cl.getFilename(file, currentDir)
				goFile := goPkg.goFiles[goFilename]
				for _, decl := range file.Decls {
					switch decl := decl.(type) {
					case *ast.GenDecl:
						for _, spec := range decl.Specs {
							switch spec := spec.(type) {
							case *ast.TypeSpec:
								var visitTypeSpec func(typeSpec *ast.TypeSpec, export bool)
								visitTypeSpec = func(typeSpec *ast.TypeSpec, export bool) {
									// if _, ok := cl.namespace[cl.types.Defs[typeSpec.Name]]; ok {
									// 	return
									// }
									// obj := cl.types.Defs[typeSpec.Name]
									visited := typeSpecVisited[typeSpec]
									// if visited && !(export && !exports[obj]) {
									// 	return
									// }
									if visited {
										return
									}

									// if !visited {
									// 	typeSpecVisited[typeSpec] = true
									// 	if structType, ok := typeSpec.Type.(*ast.StructType); ok {
									// 		for _, field := range structType.Fields.List {
									// 			if field.Names == nil {
									// 				if ident, ok := field.Type.(*ast.Ident); ok && ident.Name == "Behavior" {
									// 					goPkg.behaviors[obj] = true
									// 					export = true
									// 				}
									// 			}
									// 		}
									// 	}
									// }

									// if export {
									// 	exports[obj] = true
									// }

									ast.Inspect(typeSpec.Type, func(node ast.Node) bool {
										if ident, ok := node.(*ast.Ident); ok {
											//cl.types.Uses[ident]
											_, uses := cl.typesUses(ident)
											if typeSpec, ok := goFile.objTypeSpecs[uses]; ok {
												visitTypeSpec(typeSpec, export)
											}
										}
										return true
									})
									if !visited {
										goFile.typeSpecs = append(goFile.typeSpecs, typeSpec)
									}
								}
								visitTypeSpec(spec, false)
							case *ast.ValueSpec:
								var visitValueSpec func(valueSpec *ast.ValueSpec)
								visitValueSpec = func(valueSpec *ast.ValueSpec) {
									if valueSpecVisited[valueSpec] {
										return
									}
									valueSpecVisited[valueSpec] = true
									ast.Inspect(valueSpec, func(node ast.Node) bool {
										if ident, ok := node.(*ast.Ident); ok {
											_, uses := cl.typesUses(ident)
											if valueSpec, ok := goFile.objValueSpecs[uses]; ok {
												visitValueSpec(valueSpec)
											}
										}
										return true
									})
									// extern := false
									// for _, name := range valueSpec.Names {
									// 	if _, ok := cl.namespace[cl.types.Defs[name]]; ok {
									// 		extern = true
									// 	}
									// }
									// if !extern {
									// 	goPkg.valueSpecs = append(goPkg.valueSpecs, valueSpec)
									// }
									goFile.valueSpecs = append(goFile.valueSpecs, valueSpec)
								}
								visitValueSpec(spec)
							}
						}
					case *ast.FuncDecl:
						goFile.funcDecls = append(goFile.funcDecls, decl)
						// if _, ok := cl.namespace[cl.types.Defs[decl.Name]]; !ok {
						// 	goPkg.funcDecls = append(goPkg.funcDecls, decl)
						// }
					}
				}
			}
		}
	}

	// Generate type definitions and declarations
	for _, pkg := range pkgs {
		goPkg := cl.nameToGoPackage[pkg.Types.Name()]
		cl.currentGoPkg = goPkg
		if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
			continue
		}
		for _, goFile := range goPkg.goFiles {
			cl.currentGoFile = goFile
			for _, typeSpec := range goFile.typeSpecs {
				cl.genTypeDefn(typeSpec)
				cl.genTypeDecl(typeSpec)
			}
		}
	}

	// Generate function declarations
	for _, pkg := range pkgs {
		goPkg := cl.nameToGoPackage[pkg.Types.Name()]
		cl.currentGoPkg = goPkg
		if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
			continue
		}
		for _, goFile := range goPkg.goFiles {
			cl.currentGoFile = goFile
			for _, fd := range goFile.funcDecls {
				cl.genFuncDecl(fd)
			}
		}
	}

	// Generate global variables
	for _, pkg := range pkgs {
		goPkg := cl.nameToGoPackage[pkg.Types.Name()]
		cl.currentGoPkg = goPkg
		if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
			continue
		}
		for _, goFile := range goPkg.goFiles {
			cl.currentGoFile = goFile
			for _, valueSpec := range goFile.valueSpecs {
				for i, name := range valueSpec.Names {
					memberIdent := cl.getIdent(name)
					var value []string
					if len(valueSpec.Values) > 0 {
						text := newTextStream(2)
						cl.writeExpr(valueSpec.Values[i], text)
						text.flush()
						value = text.Lines
					}
					_, typeof := cl.typesTypeOf(valueSpec.Names[i])
					typeStr := cl.genTypeExpr(typeof, valueSpec.Pos(), "")
					member := newMemberInfo(memberIdent, typeStr, value)
					member.Const = name.Obj.Kind == ast.Con
					goFile.vars[memberIdent] = member
				}
			}
		}
	}

	// When we are using a type as a return type, function parameter, variable, field, etc..,
	// we need to identify where the type comes from so that we can update our list of include
	// files.

	typeOrigin := map[string]string{}

	// Populate the typeOrigin map with the basic primitives, since they have a known origin
	typeOrigin["void"] = "core/core"
	for _, typ := range cl.cppTypes {
		typeOrigin[typ] = "core/core"
	}

	// Populate the typeOrigin map with the types from the packages
	for _, pkg := range pkgs {
		goPkg := cl.nameToGoPackage[pkg.Types.Name()]
		for _, goFile := range goPkg.goFiles {
			for _, s := range goFile.structs {
				if _, ok := typeOrigin[s.Name]; !ok {
					typeOrigin[s.Name] = goFile.name
					typeOrigin[goPkg.name+"::"+s.Name] = goFile.name
				}
			}
		}
	}

	// Identify the types used in each go file that are not local to that file and update its include file list
	for _, goPkg := range cl.nameToGoPackage {
		for _, goFile := range goPkg.goFiles {
			for _, s := range goFile.structs {
				for _, m := range s.Members {
					if _, ok := typeOrigin[m.Type]; ok {
						include := typeOrigin[m.Type]
						if include != goFile.name {
							goFile.registerInclude(include + ".h")
						}
					}
				}
			}
		}
	}

	// Output C++ source file (.cpp)
	{
		for _, pkg := range pkgs {
			goPkg := cl.nameToGoPackage[pkg.Types.Name()]
			cl.currentGoPkg = goPkg
			if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
				continue
			}

			for _, goFile := range goPkg.goFiles {
				cl.currentGoFile = goFile

				goFile.cppSource = newTextStream(1024)
				text := goFile.cppSource

				text.writeLn("// ========================================================")
				text.writeLn("// Generated by go-cxx, please do not edit.")
				text.writeLn("// ========================================================")

				// Includes
				// C++ source file (.cpp)
				goFile.writeIncludes(text)
				// Source file includes its own header file
				text.writeLn("#include \"" + goFile.name + ".h\"")
				text.writeLn()

				// Namespace
				// C++ source file (.cpp)
				text.writeLn("namespace " + goPkg.settings.Namespace)
				text.writeLn("{")
				text.blockStart()

				// Types
				// C++ source file (.cpp)
				if len(goFile.typeSpecs) > 0 {
					text.writeLn("//", "// Types", "//")
					for _, typeSpec := range goFile.typeSpecs {
						cl.genTypeDefn(typeSpec)
						if typeDecl := cl.genTypeDecl(typeSpec); typeDecl != "" {
							text.write(typeDecl)
							text.write(";")
							text.writeLn()
						}
					}
				}

				// Function declarations (private)
				// C++ source file (.cpp)
				if len(goFile.funcDecls) > 0 {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Function declarations", "//")
					for _, fn := range goFile.functions {
						if fn.Public {
							fn.writeImpl(text, cl)
						} else {
							fn.writeDecl(text)
							fn.writeImpl(text, cl)
						}
					}
				}

				// Variables (only private)
				// C++ source file (.cpp)
				if goFile.hasPrivateVars() {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Variables", "//")
					for _, v := range goFile.vars {
						if !v.Public {
							text.write("static ")
							v.writeDecl(text)
						}
					}
				}

				// Method implementations
				// C++ source file (.cpp)
				if goFile.hasPublicStructs() {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Public types, method implementations", "//")
					for _, s := range goFile.structs {
						if s.Public {
							// Header file has declarations
							// Now we write the implementations
							s.writeMethodImplementations(text, cl)
						}
					}
				}

				if goFile.hasPrivateStructs() {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Private types", "//")
					for _, s := range goFile.structs {
						if !s.Public {
							// The structure was not public in the package, so it can be fully at the source file level.
							s.writeDecl(text)
							s.writeMethodImplementations(text, cl)
						}
					}
				}

				text.blockEnd()
				text.writeLn("}")
			}
		}
	}

	// Output C++ header file (.h)
	{
		// Namespace for every package
		// C++ header file (.h)
		for _, pkg := range pkgs {
			goPkg := cl.nameToGoPackage[pkg.Types.Name()]
			cl.currentGoPkg = goPkg
			if !goPkg.settings.ExportSource && !goPkg.settings.ExportHeader {
				continue
			}

			for _, goFile := range goPkg.goFiles {
				cl.currentGoFile = goFile

				goFile.cppHeader = newTextStream(1024)
				text := goFile.cppHeader

				// `#pragma once`
				text.write("#pragma once")
				text.writeLn()
				text.writeLn()

				// Don't re-define in generated CC
				text.writeLn("#ifndef " + goFile.getIncludeGuardIdentifier())
				text.writeLn("#define " + goFile.getIncludeGuardIdentifier())
				text.writeLn()
				text.writeLn()

				// Includes
				// C++ header file (.h)
				goFile.writeIncludes(text)
				text.writeLn()

				text.writeLn("namespace " + goPkg.settings.Namespace)
				text.writeLn("{")
				text.blockStart()

				// Types
				// C++ header file (.h)
				if len(goFile.typeSpecs) > 0 {
					text.writeLn("//", "// Types", "//")
					for _, typeSpec := range goFile.typeSpecs {
						if typeDecl := cl.genTypeDecl(typeSpec); typeDecl != "" {
							text.write(typeDecl)
							text.writeLn(";")
						}
					}
				}

				// Variables
				// C++ header file (.h)
				if goFile.hasPublicVars() {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Variables", "//")
					text.writeLn()
					for _, memberInfo := range goFile.vars {
						if memberInfo.Public {
							memberInfo.writeDecl(text)
						}
					}
				}

				// Function declarations (public)
				// C++ header file (.h)
				if len(goFile.funcDecls) > 0 {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Function declarations", "//")
					for _, fn := range goFile.functions {
						fn.writeDecl(text)
					}
				}

				// Structure (type) declarations (public)
				// C++ header file (.h)
				if goFile.hasPublicStructs() {
					text.writeLn()
					text.writeLn()
					text.writeLn("//", "// Struct declarations", "//")
					for _, s := range goFile.structs {
						if s.Public {
							s.writeDecl(text)
						}
					}
				}

				// Closing namespace
				text.blockEnd()
				text.writeLn("}")

				// Closing include guard
				text.writeLn()
				text.writeLn("#endif")
			}
		}
	}

	return true
}

// Main
func main() {
	nArgs := len(os.Args)
	if nArgs < 1 {
		fmt.Println("usage: go-cxx <main_package_path>")
		return
	}

	cl := newCompiler(os.Args[1]) // Create compiler
	if !cl.compile() {            // Compile and exit if there were errors
		fmt.Println(cl.errors)
		os.Exit(1)
	}

	// Emit all .cpp and .h files
	for _, pkg := range cl.nameToGoPackage {
		for _, goFile := range pkg.goFiles {
			if goFile.settings.ExportHeader && goFile.cppHeader != nil {
				relFilePath := "output/" + goFile.name + ".h"
				content := goFile.cppHeader.string()
				exportFile(relFilePath, content)
			}
			if goFile.settings.ExportSource && goFile.cppSource != nil {
				relFilePath := "output/" + goFile.name + ".cpp"
				content := goFile.cppSource.string()
				exportFile(relFilePath, content)
			}
		}
	}
}

func exportFile(fileName string, content string) {
	// Write C++ source file
	// If there is an existing file on disk, compare the content
	// and only overwrite if different

	out := os.Stdout
	errors := os.Stderr

	if err := os.MkdirAll(filepath.Dir(fileName), 0755); err != nil {
		fmt.Fprintf(errors, "error creating directory %s: %v\n", fileName, err)
		return
	}

	// Check if file exists
	if _, err := os.Stat(fileName); err == nil {
		// File exists, compare content
		existingContent, err := os.ReadFile(fileName)
		if err != nil {
			fmt.Fprintf(errors, "error reading file %s: %v\n", fileName, err)
			return
		}
		if string(existingContent) == content {
			fmt.Fprintf(out, "File %s is up to date\n", fileName)
			return
		}

		// File exists and content is different, overwrite
		fmt.Fprintf(out, "File %s exists and is different, overwriting\n", fileName)
	} else if !os.IsNotExist(err) {
		// Error checking file existence
		fmt.Fprintf(errors, "error checking file %s: %v\n", fileName, err)
		return
	}

	// Write new content to file
	if err := os.WriteFile(fileName, []byte(content), 0644); err != nil {
		fmt.Fprintf(errors, "error writing file %s: %v\n", fileName, err)
		return
	}

	fmt.Fprintf(out, "Wrote file %s\n", fileName)
}
