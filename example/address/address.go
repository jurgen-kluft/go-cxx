package naddress

// ---------------------------------------------------
// Settings of this package for the `go-cxx` compiler
// ---------------------------------------------------
import go_cxx "github.com/jurgen-kluft/go-cxx/core"

var __settings = go_cxx.Settings{
	ExportSource: true,
	ExportHeader: true,
	Namespace:    "naddress",
	Includes:     []string{},
}

// ---------------------------------------------------
// ---------------------------------------------------

type Address struct {
	nameOfCity     string
	postalCode     int
	street         string
	number         int
	privateAddress bool
}

func NewAddress(city string, postalCode int, street string, number int) Address {
	return Address{
		nameOfCity:     city,
		postalCode:     postalCode,
		street:         street,
		number:         number,
		privateAddress: false,
	}
}

func (a Address) NameOfCity() string {
	return a.nameOfCity
}

func (a Address) PostalCode() int {
	return a.postalCode
}

func (a Address) Street() string {
	return a.street
}

func (a Address) Number() int {
	return a.number
}

func (a Address) isPrivate() bool {
	return a.privateAddress
}
