package person

// ---------------------------------------------------
// Settings of this package for the `go-cxx` compiler
// ---------------------------------------------------
import go_cxx "github.com/jurgen-kluft/go-cxx/core"

var __settings = go_cxx.Settings{
	Export:    true,
	Namespace: "nperson",
	Includes: []string{
		"go-cxx-core.h",
		"go-cxx/cdb/go-cxx-db.h",
	},
}

// ---------------------------------------------------
// ---------------------------------------------------

type Person struct {
	age    int
	health float32
	iq     int
}

var Population int

func NewPerson(age int, health float32, iq int) Person {
	return Person{
		age:    age,
		health: health,
		iq:     iq,
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

func (p *Person) Grow() {
	p.age += 1
}

type AgeAdder func(i int) int

func (p *Person) GetAgeAdder() AgeAdder {
	return func(i int) int {
		return p.age + i
	}
}
