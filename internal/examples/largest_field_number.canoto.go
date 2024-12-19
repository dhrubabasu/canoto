// Code generated by canoto. DO NOT EDIT.
// versions:
// 	canoto v0.3.0-dev
// source: largest_field_number.go

package examples

import (
	"io"
	"sync/atomic"
	"unicode/utf8"

	"github.com/StephenButtolph/canoto"
)

// Ensure that unused imports do not error
var (
	_ = io.ErrUnexpectedEOF
	_ = utf8.ValidString
)

const (
	canoto__LargestFieldNumber__Int32__tag = "\xf8\xff\xff\xff\x0f" // canoto.Tag(536870911, canoto.Varint)
)

type canotoData_LargestFieldNumber struct {
	// Enforce noCopy before atomic usage.
	// See https://github.com/StephenButtolph/canoto/pull/32
	_ atomic.Int64

	size int
}

// UnmarshalCanoto unmarshals a Canoto-encoded byte slice into the struct.
//
// OneOf fields are cached during the unmarshaling process.
//
// The struct is not cleared before unmarshaling, any fields not present in the
// bytes will retain their previous values. If a OneOf field was previously
// cached as being set, attempting to unmarshal that OneOf again will return
// canoto.ErrDuplicateOneOf.
func (c *LargestFieldNumber[_]) UnmarshalCanoto(bytes []byte) error {
	r := canoto.Reader{
		B: bytes,
	}
	return c.UnmarshalCanotoFrom(&r)
}

// UnmarshalCanotoFrom populates the struct from a canoto.Reader. Most users
// should just use UnmarshalCanoto.
//
// OneOf fields are cached during the unmarshaling process.
//
// The struct is not cleared before unmarshaling, any fields not present in the
// bytes will retain their previous values. If a OneOf field was previously
// cached as being set, attempting to unmarshal that OneOf again will return
// canoto.ErrDuplicateOneOf.
//
// This function enables configuration of reader options.
func (c *LargestFieldNumber[_]) UnmarshalCanotoFrom(r *canoto.Reader) error {
	var minField uint32
	for canoto.HasNext(r) {
		field, wireType, err := canoto.ReadTag(r)
		if err != nil {
			return err
		}
		if field < minField {
			return canoto.ErrInvalidFieldOrder
		}

		switch field {
		case 536870911:
			if wireType != canoto.Varint {
				return canoto.ErrUnexpectedWireType
			}

			if err := canoto.ReadInt(r, &c.Int32); err != nil {
				return err
			}
			if canoto.IsZero(c.Int32) {
				return canoto.ErrZeroValue
			}
		default:
			return canoto.ErrUnknownField
		}

		minField = field + 1
	}
	return nil
}

// ValidCanoto validates that the struct can be correctly marshaled into the
// Canoto format.
//
// Specifically, ValidCanoto ensures:
// 1. All OneOfs are specified at most once.
// 2. All strings are valid utf-8.
// 3. All custom fields are ValidCanoto.
func (c *LargestFieldNumber[_]) ValidCanoto() bool {
	return true
}

// CalculateCanotoCache populates size and OneOf caches based on the current
// values in the struct.
//
// It is not safe to call this function concurrently.
func (c *LargestFieldNumber[_]) CalculateCanotoCache() {
	c.canotoData.size = 0
	if !canoto.IsZero(c.Int32) {
		c.canotoData.size += len(canoto__LargestFieldNumber__Int32__tag) + canoto.SizeInt(c.Int32)
	}
}

// CachedCanotoSize returns the previously calculated size of the Canoto
// representation from CalculateCanotoCache.
//
// If CalculateCanotoCache has not yet been called, it will return 0.
//
// If the struct has been modified since the last call to CalculateCanotoCache,
// the returned size may be incorrect.
func (c *LargestFieldNumber[_]) CachedCanotoSize() int {
	return c.canotoData.size
}

// MarshalCanoto returns the Canoto representation of this struct.
//
// It is assumed that this struct is ValidCanoto.
//
// It is not safe to call this function concurrently.
func (c *LargestFieldNumber[_]) MarshalCanoto() []byte {
	c.CalculateCanotoCache()
	w := canoto.Writer{
		B: make([]byte, 0, c.CachedCanotoSize()),
	}
	c.MarshalCanotoInto(&w)
	return w.B
}

// MarshalCanotoInto writes the struct into a canoto.Writer. Most users should
// just use MarshalCanoto.
//
// It is assumed that CalculateCanotoCache has been called since the last
// modification to this struct.
//
// It is assumed that this struct is ValidCanoto.
//
// It is not safe to call this function concurrently.
func (c *LargestFieldNumber[_]) MarshalCanotoInto(w *canoto.Writer) {
	if !canoto.IsZero(c.Int32) {
		canoto.Append(w, canoto__LargestFieldNumber__Int32__tag)
		canoto.AppendInt(w, c.Int32)
	}
}
