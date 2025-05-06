package naddress

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

func (a Address) isLuckyNumber() bool {
	switch a.number {
	case 4:
		return false
	case 13:
		return false
	}
	return true
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

func (a *Address) SetPrivateAddress() {
	a.privateAddress = true
}

func (a Address) Number() int {
	return a.number + 1
}

func (a *Address) SetNumber(number int, p bool) {
	a.number = number
	a.privateAddress = p
}

func (a Address) isPrivate() bool {
	return a.privateAddress
}

func Test() {
	a := NewAddress("Shanghai", 1010, "Big square", 6)
	a.NameOfCity()
	a.PostalCode()
	a.Street()
	a.Number()
	a.SetPrivateAddress()
	a.SetNumber(42, true)
}
