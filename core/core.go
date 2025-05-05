package ngo_cxx

// ExportSource & ExportHeader:
// When ExportHeader == false, the C++ header file is not exported AND the C++ source file is not exported
// When ExportHeader == true, the C++ header file is exported, and only if ExportSource == true, the C++ source file is exported

// IsInstance:
// When ExportHeader == false and IsInstance == true it means that the external C++ code is not a namespace but an instance of a class.
// For example, in C++ there could be a global instance of a class/struct called `Serial` which exposes all the functions and necessary
// members/variables (see example/use_serial).

type Settings struct {
	ExportSource bool     //
	ExportHeader bool     //
	Instance     string   // Object (Name.) used in the C++ code
	Namespace    string   // Namespace (Name::) used in the C++ code
	OutputPrefix string   // Prefix for the output files
	Includes     []string // List of includes to be added to the C++ code
}

func NewSettings() *Settings {
	return &Settings{
		ExportSource: false,      //
		ExportHeader: false,      //
		Instance:     "",         // e.g. "Serial"
		Namespace:    "ngo_cxx",  // e.g. "nfoo"
		OutputPrefix: "",         //
		Includes:     []string{}, //
	}
}
