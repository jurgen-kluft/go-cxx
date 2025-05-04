package use_serial

import (
	go_cxx "github.com/jurgen-kluft/go-cxx/core"
	serial "github.com/jurgen-kluft/go-cxx/example/serial"
)

// ---------------------------------------------------
// Settings of this package for the `go-cxx` compiler
// ---------------------------------------------------
var __settings = go_cxx.Settings{
	ExportSource: true,
	ExportHeader: true,
	Instance:     "",
	Namespace:    "",
	Includes: []string{
		"go-cxx-core.h",
		"go-cxx/cdb/go-cxx-db.h",
	},
}

// ---------------------------------------------------
// ---------------------------------------------------

func Test() {
	// Test function to check if the package is working
	// This is just a placeholder and should be replaced with actual tests
	serial.Baud = serial.BaudRate9600
	serial.Println("Serial package test function")
}
