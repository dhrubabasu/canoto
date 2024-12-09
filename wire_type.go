package canoto

import "errors"

const (
	Varint WireType = iota
	I64
	Len
	_ // SGROUP is deprecated and not supported
	_ // EGROUP is deprecated and not supported
	I32

	MaxFieldNumber = 1<<29 - 1

	wireTypeLength = 3
	wireTypeMask   = 0x07
)

var ErrInvalidWireType = errors.New("invalid wire type")

type WireType byte

func (w WireType) IsValid() bool {
	switch w {
	case Varint, I64, Len, I32:
		return true
	default:
		return false
	}
}

func (w WireType) String() string {
	switch w {
	case Varint:
		return "Varint"
	case I64:
		return "I64"
	case Len:
		return "Len"
	case I32:
		return "I32"
	default:
		return "Invalid"
	}
}
