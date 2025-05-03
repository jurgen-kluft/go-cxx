package foo

// ---------------------------------------------------
// Settings of this package for the `go-cxx` compiler
// ---------------------------------------------------
import go_cxx "github.com/jurgen-kluft/go-cxx/core"

var __settings = go_cxx.Settings{
	Export:    false,
	Namespace: "nfoo",
	Includes: []string{
		"go-cxx-core.h",
		"go-cxx/go-cxx-foo.h",
	},
}

// ---------------------------------------------------
// ---------------------------------------------------

type Foo struct {
	val int
}

type Bar struct {
	X, Y int
}

func (f *Foo) Val() int {
	return f.val
}

func NewFoo(val int) Foo {
	return Foo{val}
}
