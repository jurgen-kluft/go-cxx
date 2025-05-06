package ngo_cxx

// import (
// 	"encoding/json"
// 	"os"
// )

// // ExportSource & ExportHeader:
// // When ExportHeader == false, the C++ header file is not exported AND the C++ source file is not exported
// // When ExportHeader == true, the C++ header file is exported, and only if ExportSource == true, the C++ source file is exported

// // IsInstance:
// // When ExportHeader == false and IsInstance == true it means that the external C++ code is not a namespace but an instance of a class.
// // For example, in C++ there could be a global instance of a class/struct called `Serial` which exposes all the functions and necessary
// // members/variables (see example/use_serial).

type Settings struct {
	ExportSource bool     `json:"ExportSource"` //
	ExportHeader bool     `json:"ExportHeader"` //
	Instance     string   `json:"Instance"`     // Object (Name.) used in the C++ code
	Namespace    string   `json:"Namespace"`    // Namespace (Name::) used in the C++ code
	OutputPrefix string   `json:"OutputPrefix"` // Prefix for the output files
	Includes     []string `json:"Includes"`     // List of includes to be added to the C++ code
}

func NewSettings(namespace string) *Settings {
	return &Settings{
		ExportSource: true,       //
		ExportHeader: true,       //
		Instance:     "",         // e.g. "Serial"
		Namespace:    namespace,  // e.g. "nfoo"
		OutputPrefix: "",         //
		Includes:     []string{}, //
	}
}

// func LoadSettings(namespace string, filepath string) (*Settings, error) {
// 	if _, err := os.Stat(filepath); err != nil {
// 		return nil, nil
// 	}
// 	settings := NewSettings(namespace)
// 	bytes, err := os.ReadFile(filepath)
// 	if err != nil {
// 		return nil, err
// 	}
// 	if err := json.Unmarshal(bytes, settings); err != nil {
// 		return nil, err
// 	}
// 	return settings, nil
// }
