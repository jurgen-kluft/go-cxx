package nperson

import (
	naddress "github.com/jurgen-kluft/go-cxx/example/address"
)

type Person struct {
	age     int
	health  float64
	iq      int
	address naddress.Address
	secret  Secret
}

var Population int

func NewPerson(age int, health float64, iq int) Person {
	Population++
	return Person{
		age:     age,
		health:  health,
		iq:      iq,
		address: naddress.NewAddress("Amsterdam", 1012, "Damstraat", 1),
	}
}

func (this *Person) Constructor(age int, health float64, iq int) *Person {
	this.age = age
	this.health = health
	this.iq = iq
	this.secret = Secret{}
	Population++
	return this
}

func UsageCase() {
	age := 42
	health := 0.8
	iq := 120
	//person := core.Allocate[Person]().Constructor(age, health, iq)
	person := new(Person).Constructor(age, health, iq)
	person.SetSecret(NewSecret("1234"))
}

func (p Person) GetAge() int {
	return p.age
}

func (p Person) GetHealth() float64 {
	return p.health
}

func (p Person) GetIQ() int {
	return p.iq
}

func (p Person) GetAddress() naddress.Address {
	return p.address
}

func (p *Person) SetAddress(a naddress.Address) {
	p.address = a
}

func (p Person) GetSecret() Secret {
	return p.secret
}

func (p *Person) SetSecret(s Secret) {
	p.secret = s
}

func (p *Person) GetGrow() {
	p.age += 1
}

type AgeAdder func(i int) int

func (p *Person) GetAgeAdder() AgeAdder {
	return func(i int) int {
		return p.age + i
	}
}
