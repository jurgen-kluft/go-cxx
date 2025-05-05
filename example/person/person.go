package nperson

import (
	go_cxx "github.com/jurgen-kluft/go-cxx/core"
	naddress "github.com/jurgen-kluft/go-cxx/example/address"
)

// ---------------------------------------------------
// Settings of this package for the `go-cxx` compiler
// ---------------------------------------------------
var __settings = go_cxx.Settings{
	ExportSource: true,
	ExportHeader: true,
	Instance:     "",
	Namespace:    "nperson",
	Includes:     []string{},
}

// ---------------------------------------------------
// ---------------------------------------------------

type Person struct {
	age     int
	health  float32
	iq      int
	address naddress.Address
	secret  Secret
}

var Population int

func NewPerson(age int, health float32, iq int) Person {
	return Person{
		age:    age,
		health: health,
		iq:     iq,
		secret: Secret{},
	}
}

func (p Person) Age() int {
	return p.age
}

func (p Person) Health() float32 {
	return p.health
}

func (p Person) IQ() int {
	return p.iq
}

func (p Person) Address() naddress.Address {
	return p.address
}

func (p *Person) SetAddress(a naddress.Address) {
	p.address = a
}

func (p Person) Secret() Secret {
	return p.secret
}

func (p *Person) SetSecret(s Secret) {
	p.secret = s
}

func (p *Person) Grow() {
	p.age += 1
}

type AgeAdder func(i int) int

func (p *Person) GetAgeAdder() AgeAdder {
	return func(i int) int {
		return p.age + i
	}
}
