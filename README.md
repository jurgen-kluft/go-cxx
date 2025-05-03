# Go to C++

WIP

## Example: A Go struct

Here an example of how a struct in Golang is converted to C++.

```go
type Person struct {
    FirstName string
    LastName  string
    Age       int
    Health    float64
    IQ        int
}

func (p Person) FirstName() string {
    return p.FirstName
}

func (p Person) LastName() string {
    return p.LastName
}

func (p Person) Age() int {
    return p.Age
}

func (p *Person) SetAge(age int) {
    p.Age = age
}

func (p Person) Health() float64 {
    return p.Health
}

func (p Person) IQ() int {
    return p.IQ
}

func (p Person) isValid() bool {
    return p.Age > 0 && p.Health > 0 && p.IQ > 0
}
```

The above code is a Go struct with methods. The following is the C++ code that is generated from it by the Go to C++ compiler.

```cpp
struct Person {
    string FirstName;
    string LastName;
    int Age;
    double Health;
    int IQ;

    string FirstName() const {
        return FirstName;
    }

    string LastName() const {
        return LastName;
    }

    int Age() const {
        return Age;
    }

    void SetAge(int age) {
        Age = age;
    }
    
    double Health() const {
        return Health;
    }

    int IQ() const {
        return IQ;
    }

private:
    bool isValid() const {
        return Age > 0 && Health > 0 && IQ > 0;
    }
};
```