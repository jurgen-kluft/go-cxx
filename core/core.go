package ngo_cxx

type Settings struct {
	ExportSource bool     // When ExportSource == true, the C++ source file is exported
	ExportHeader bool     // When ExportHeader == true, the C++ header file is exported
	IsInstance   bool     // When export == false, IsInstance == true means that the external C++ code is not a namespace but an instance of a class
	Namespace    string   // Namespace or class name used in the C++ code
	OutputPrefix string   // Prefix for the output files
	Includes     []string // List of includes to be added to the C++ code
}

func NewSettings(namespace string) *Settings {
	return &Settings{
		ExportSource: false,
		ExportHeader: false,
		IsInstance:   false,
		Namespace:    namespace,
		OutputPrefix: "__core_",
		Includes:     []string{},
	}
}
