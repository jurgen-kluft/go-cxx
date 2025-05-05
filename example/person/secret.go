package nperson

// ---------------------------------------------------
// ---------------------------------------------------

type Secret struct {
	password string
}

func NewSecret(password string) Secret {
	return Secret{
		password: password,
	}
}

func (s Secret) Password() string {
	return s.password
}
