package big

import (
	"math/big"
	"reflect"

	"github.com/StephenButtolph/canoto"
)

var (
	_ canoto.Field            = (*Int)(nil)
	_ canoto.FieldMaker[*Int] = (*Int)(nil)
)

type Int struct {
	Int *big.Int
}

func (*Int) CanotoSpec(...reflect.Type) *canoto.Spec {
	// Nil indicates that the type does not have a valid spec. This type will be
	// treated as opaque bytes.
	return nil
}

func (*Int) MakeCanoto() *Int {
	return new(Int)
}

func (i *Int) UnmarshalCanotoFrom(r canoto.Reader) error {
	if i.Int == nil {
		i.Int = new(big.Int)
	}
	i.Int.SetBytes(r.B)
	if i.CachedCanotoSize() != len(r.B) {
		return canoto.ErrPaddedZeroes
	}
	return nil
}

func (*Int) ValidCanoto() bool     { return true }
func (*Int) CalculateCanotoCache() {}

func (i *Int) CachedCanotoSize() int {
	if i == nil || i.Int == nil {
		return 0
	}
	return (i.Int.BitLen() + 7) / 8
}

func (i *Int) MarshalCanotoInto(w canoto.Writer) canoto.Writer {
	if i == nil || i.Int == nil {
		return w
	}
	startIndex := len(w.B)
	w.B = append(w.B, make([]byte, i.CachedCanotoSize())...)
	i.Int.FillBytes(w.B[startIndex:])
	return w
}
