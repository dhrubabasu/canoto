package generate

import (
	"encoding/hex"
	"errors"
	"fmt"
	"go/parser"
	"go/token"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/StephenButtolph/canoto"
)

const (
	goExtension     = ".go"
	canotoExtension = ".canoto.go"
)

var errNonGoExtension = errors.New("file must be a go file")

// Canoto generates the canoto serialization logic for the provided file.
func Canoto(inputFilePath string) error {
	extension := filepath.Ext(inputFilePath)
	if extension != goExtension {
		return fmt.Errorf("%w not %q", errNonGoExtension, extension)
	}

	// Create a new parser
	fs := token.NewFileSet()
	f, err := parser.ParseFile(fs, inputFilePath, nil, parser.ParseComments)
	if err != nil {
		return err
	}

	packageName, messages, err := parse(fs, f)
	if err != nil {
		return err
	}
	if len(messages) == 0 {
		return nil
	}

	outputFilePath := inputFilePath[:len(inputFilePath)-len(goExtension)] + canotoExtension
	outputFile, err := os.Create(outputFilePath)
	if err != nil {
		return err
	}
	defer outputFile.Close()

	return writeCanoto(outputFile, inputFilePath, packageName, messages)
}

func writeCanoto(w io.Writer, source string, packageName string, messages []message) error {
	const fileTemplate = `// Code generated by canoto. DO NOT EDIT.
// versions:
// 	canoto ${version}
// source: ${source}

package ${package}

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
`
	err := writeTemplate(w, fileTemplate, map[string]string{
		"version": canoto.Version,
		"source":  source,
		"package": packageName,
	})
	if err != nil {
		return err
	}

	for _, m := range messages {
		if err := writeStruct(w, m); err != nil {
			return err
		}
	}
	return nil
}

func writeStruct(w io.Writer, m message) error {
	const structTemplate = `
const (
${tagConstants})

type canotoData_${structName} struct {
	// Enforce noCopy before atomic usage.
	// See https://github.com/StephenButtolph/canoto/pull/32
	_ atomic.Int64

${cache}}

// UnmarshalCanoto unmarshals a Canoto-encoded byte slice into the struct.
//
// The struct is not cleared before unmarshaling, any fields not present in the
// bytes will retain their previous values.
func (c *${structName}${generics}) UnmarshalCanoto(bytes []byte) error {
	r := canoto.Reader{
		B: bytes,
	}
	return c.UnmarshalCanotoFrom(&r)
}

// UnmarshalCanotoFrom populates the struct from a canoto.Reader. Most users
// should just use UnmarshalCanoto.
//
// The struct is not cleared before unmarshaling, any fields not present in the
// bytes will retain their previous values.
//
// This function enables configuration of reader options.
func (c *${structName}${generics}) UnmarshalCanotoFrom(r *canoto.Reader) error {
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
${unmarshal}		default:
			return canoto.ErrUnknownField
		}

		minField = field + 1
	}
	return nil
}

// ValidCanoto validates that the struct can be correctly marshaled into the
// Canoto format.
//
// Specifically, ValidCanoto ensures that all strings are valid utf-8 and all
// custom types are ValidCanoto.
func (c *${structName}${generics}) ValidCanoto() bool {
${valid}	return true
}

// CalculateCanotoSize calculates the size of the Canoto representation and
// caches it.
//
// It is not safe to call this function concurrently.
func (c *${structName}${generics}) CalculateCanotoSize() int {
	c.canotoData.size = 0
${size}	return c.canotoData.size
}

// CachedCanotoSize returns the previously calculated size of the Canoto
// representation from CalculateCanotoSize.
//
// If CalculateCanotoSize has not yet been called, it will return 0.
//
// If the struct has been modified since the last call to CalculateCanotoSize,
// the returned size may be incorrect.
func (c *${structName}${generics}) CachedCanotoSize() int {
	return c.canotoData.size
}

// MarshalCanoto returns the Canoto representation of this struct.
//
// It is assumed that this struct is ValidCanoto.
//
// It is not safe to call this function concurrently.
func (c *${structName}${generics}) MarshalCanoto() []byte {
	w := canoto.Writer{
		B: make([]byte, 0, c.CalculateCanotoSize()),
	}
	c.MarshalCanotoInto(&w)
	return w.B
}

// MarshalCanotoInto writes the struct into a canoto.Writer. Most users should
// just use MarshalCanoto.
//
// It is assumed that CalculateCanotoSize has been called since the last
// modification to this struct.
//
// It is assumed that this struct is ValidCanoto.
//
// It is not safe to call this function concurrently.
func (c *${structName}${generics}) MarshalCanotoInto(w *canoto.Writer) {
${marshal}}
`

	return writeTemplate(w, structTemplate, map[string]string{
		"tagConstants": makeTagConstants(m),
		"structName":   m.name,
		"generics":     makeGenerics(m),
		"cache":        makeCache(m),
		"unmarshal":    makeUnmarshal(m),
		"valid":        makeValid(m),
		"size":         makeSize(m),
		"marshal":      makeMarshal(m),
	})
}

func makeGenerics(m message) string {
	if m.numTypes == 0 {
		return ""
	}

	var s strings.Builder
	_, _ = s.WriteString("[")
	for i := range m.numTypes {
		if i != 0 {
			_, _ = s.WriteString(", ")
		}
		_, _ = s.WriteString("_")
	}
	_, _ = s.WriteString("]")
	return s.String()
}

func makeTagConstants(m message) string {
	const tagSizeOverhead = len("canoto______tag")
	var (
		largestTagConstSize int
		largestTagSize      int
	)
	for _, f := range m.fields {
		tagConstSize := tagSizeOverhead + len(m.canonicalizedName) + len(f.canonicalizedName)
		largestTagConstSize = max(largestTagConstSize, tagConstSize)

		wireType := f.canotoType.WireType()
		tagBytes := canoto.Tag(f.fieldNumber, wireType)
		tagSize := 2 + 4*len(tagBytes)
		largestTagSize = max(largestTagSize, tagSize)
	}

	var (
		template = fmt.Sprintf("\t%%-%ds = %%-%ds // canoto.Tag(%%d, canoto.%%s)\n",
			largestTagConstSize,
			largestTagSize,
		)
		s strings.Builder
	)
	for _, f := range m.fields {
		tag := fmt.Sprintf("canoto__%s__%s__tag", m.canonicalizedName, f.canonicalizedName)

		var tagString strings.Builder
		_, _ = tagString.WriteString(`"`)
		wireType := f.canotoType.WireType()
		tagBytes := canoto.Tag(f.fieldNumber, wireType)
		tagHex := hex.EncodeToString(tagBytes)
		for i := 0; i < len(tagHex); i += 2 {
			_, _ = fmt.Fprintf(&tagString, "\\x%s", tagHex[i:i+2])
		}
		_, _ = tagString.WriteString(`"`)

		_, _ = fmt.Fprintf(&s, template, tag, &tagString, f.fieldNumber, wireType)
	}
	return s.String()
}

func makeCache(m message) string {
	const (
		sizeVar    = "size"
		sizeSuffix = "Size"
	)
	largestNameSize := len(sizeVar)
	for _, f := range m.fields {
		if !f.canotoType.IsRepeated() || !f.canotoType.IsVarint() {
			continue
		}

		largestNameSize = max(largestNameSize, len(f.name)+len(sizeSuffix))
	}

	var (
		template = fmt.Sprintf("\t%%-%ds int\n", largestNameSize)
		s        strings.Builder
	)
	_, _ = fmt.Fprintf(&s, template, sizeVar)
	for _, f := range m.fields {
		if !f.canotoType.IsRepeated() || !f.canotoType.IsVarint() {
			continue
		}

		_, _ = fmt.Fprintf(&s, template, f.name+sizeSuffix)
	}
	return s.String()
}

func makeUnmarshal(m message) string {
	const (
		intTemplate = `		case ${fieldNumber}:
			if wireType != canoto.${wireType} {
				return canoto.ErrUnexpectedWireType
			}
			if err := canoto.Read${suffix}(r, &c.${fieldName}); err != nil {
				return err
			}
			if canoto.IsZero(c.${fieldName}) {
				return canoto.ErrZeroValue
			}
`
		fixedRepeatedIntTemplate = `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}

			remainingBytes := r.B
			r.B = msgBytes
			for i := range c.${fieldName} {
				if err := canoto.Read${suffix}(r, &c.${fieldName}[i]); err != nil {
					r.B = remainingBytes
					return err
				}
			}
			hasNext := canoto.HasNext(r)
			r.B = remainingBytes
			if hasNext {
				return io.ErrUnexpectedEOF
			}
			if canoto.IsZero(c.${fieldName}) {
				return canoto.ErrZeroValue
			}
`
		repeatedFixedSizeTemplate = `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}

			numMsgBytes := uint(len(msgBytes))
			if numMsgBytes == 0 {
				return canoto.ErrZeroValue
			}
			if numMsgBytes%canoto.Size${suffix} != 0 {
				return canoto.ErrInvalidLength
			}

			remainingBytes := r.B
			r.B = msgBytes
			c.${fieldName} = canoto.MakeSlice(c.${fieldName}, int(numMsgBytes/canoto.Size${suffix}))
			for i := range c.${fieldName} {
				if err := canoto.Read${suffix}(r, &c.${fieldName}[i]); err != nil {
					r.B = remainingBytes
					return err
				}
			}
			r.B = remainingBytes
`
		bytesTemplate = `		case ${fieldNumber}:
			if wireType != canoto.${wireType} {
				return canoto.ErrUnexpectedWireType
			}
			if err := canoto.Read${suffix}(r, &c.${fieldName}); err != nil {
				return err
			}
			if len(c.${fieldName}) == 0 {
				return canoto.ErrZeroValue
			}
`
		repeatedBytesTemplate = `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			remainingBytes := r.B
			originalUnsafe := r.Unsafe
			r.Unsafe = true
			err := canoto.ReadBytes(r, new([]byte))
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}

			count, err := canoto.CountBytes(r.B, canoto__${escapedStructName}__${escapedFieldName}__tag)
			if err != nil {
				return err
			}
			c.${fieldName} = canoto.MakeSlice(c.${fieldName}, 1+count)

			r.B = remainingBytes
			if err := canoto.Read${suffix}(r, &c.${fieldName}[0]); err != nil {
				return err
			}
			for i := range count {
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]
				if err := canoto.Read${suffix}(r, &c.${fieldName}[1+i]); err != nil {
					return err
				}
			}
`
		fixedRepeatedBytes = `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			if err := canoto.Read${suffix}(r, &c.${fieldName}[0]); err != nil {
				return err
			}

			isZero := len(c.${fieldName}[0]) == 0
			const numToRead = uint(len(c.${fieldName}) - 1)
			for i := range numToRead {
				if !canoto.HasPrefix(r.B, canoto__${escapedStructName}__${escapedFieldName}__tag) {
					return canoto.ErrUnknownField
				}
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]
				if err := canoto.Read${suffix}(r, &c.${fieldName}[1+i]); err != nil {
					return err
				}
				isZero = isZero && len(c.${fieldName}[1+i]) == 0
			}
			if isZero {
				return canoto.ErrZeroValue
			}
`
	)
	return writeMessage(m, messageTemplate{
		ints: typeTemplate{
			single: intTemplate,
			repeated: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}
			if len(msgBytes) == 0 {
				return canoto.ErrZeroValue
			}

			remainingBytes := r.B
			r.B = msgBytes
			c.${fieldName} = canoto.MakeSlice(c.${fieldName}, canoto.CountInts(msgBytes))
			for i := range c.${fieldName} {
				if err := canoto.Read${suffix}(r, &c.${fieldName}[i]); err != nil {
					r.B = remainingBytes
					return err
				}
			}
			hasNext := canoto.HasNext(r)
			r.B = remainingBytes
			if hasNext {
				return canoto.ErrInvalidLength
			}
`,
			fixedRepeated: fixedRepeatedIntTemplate,
		},
		fints: typeTemplate{
			single:        intTemplate,
			repeated:      repeatedFixedSizeTemplate,
			fixedRepeated: fixedRepeatedIntTemplate,
		},
		bools: typeTemplate{
			single:        intTemplate,
			repeated:      repeatedFixedSizeTemplate,
			fixedRepeated: fixedRepeatedIntTemplate,
		},
		strings: typeTemplate{
			single:        bytesTemplate,
			repeated:      repeatedBytesTemplate,
			fixedRepeated: fixedRepeatedBytes,
		},
		bytesTemplate:         bytesTemplate,
		repeatedBytesTemplate: repeatedBytesTemplate,
		fixedBytesTemplate: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			var length int64
			if err := canoto.ReadInt(r, &length); err != nil {
				return err
			}

			const (
				expectedLength      = len(c.${fieldName})
				expectedLengthInt64 = int64(expectedLength)
			)
			if length != expectedLengthInt64 {
				return canoto.ErrInvalidLength
			}
			if expectedLength > len(r.B) {
				return io.ErrUnexpectedEOF
			}

			copy(c.${fieldName}[:], r.B)
			if canoto.IsZero(c.${fieldName}) {
				return canoto.ErrZeroValue
			}
			r.B = r.B[expectedLength:]
`,
		repeatedFixedBytesTemplate: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			var length int64
			if err := canoto.ReadInt(r, &length); err != nil {
				return err
			}

			const (
				expectedLength      = len(c.${fieldName}[0])
				expectedLengthInt64 = int64(expectedLength)
			)
			if length != expectedLengthInt64 {
				return canoto.ErrInvalidLength
			}
			if expectedLength > len(r.B) {
				return io.ErrUnexpectedEOF
			}

			firstEntry := r.B[:expectedLength]
			r.B = r.B[expectedLength:]
			count, err := canoto.CountBytes(r.B, canoto__${escapedStructName}__${escapedFieldName}__tag)
			if err != nil {
				return err
			}

			c.${fieldName} = canoto.MakeSlice(c.${fieldName}, 1+count)
			copy(c.${fieldName}[0][:], firstEntry)
			for i := range count {
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]
				if err := canoto.ReadInt(r, &length); err != nil {
					return err
				}
				if length != expectedLengthInt64 {
					return canoto.ErrInvalidLength
				}
				if expectedLength > len(r.B) {
					return io.ErrUnexpectedEOF
				}

				copy(c.${fieldName}[1+i][:], r.B)
				r.B = r.B[expectedLength:]
			}
`,
		fixedRepeatedBytesTemplate: fixedRepeatedBytes,
		fixedRepeatedFixedBytesTemplate: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			var length int64
			if err := canoto.ReadInt(r, &length); err != nil {
				return err
			}

			const (
				expectedLength      = len(c.${fieldName}[0])
				expectedLengthInt64 = int64(expectedLength)
			)
			if length != expectedLengthInt64 {
				return canoto.ErrInvalidLength
			}
			if expectedLength > len(r.B) {
				return io.ErrUnexpectedEOF
			}

			copy(c.${fieldName}[0][:], r.B)
			r.B = r.B[expectedLength:]
			const numToRead = uint(len(c.${fieldName}) - 1)
			for i := range numToRead {
				if !canoto.HasPrefix(r.B, canoto__${escapedStructName}__${escapedFieldName}__tag) {
					return canoto.ErrUnknownField
				}
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]

				if err := canoto.ReadInt(r, &length); err != nil {
					return err
				}
				if length != expectedLengthInt64 {
					return canoto.ErrInvalidLength
				}
				if expectedLength > len(r.B) {
					return io.ErrUnexpectedEOF
				}

				copy(c.${fieldName}[1+i][:], r.B)
				r.B = r.B[expectedLength:]
			}
			if canoto.IsZero(c.${fieldName}) {
				return canoto.ErrZeroValue
			}
`,
		customs: typeTemplate{
			single: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}
			if len(msgBytes) == 0 {
				return canoto.ErrZeroValue
			}

			remainingBytes := r.B
			r.B = msgBytes
			err = c.${fieldName}.UnmarshalCanotoFrom(r)
			r.B = remainingBytes
			if err != nil {
				return err
			}
`,
			repeated: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}

			remainingBytes := r.B
			count, err := canoto.CountBytes(remainingBytes, canoto__${escapedStructName}__${escapedFieldName}__tag)
			if err != nil {
				return err
			}

			c.${fieldName} = canoto.MakeSlice(c.${fieldName}, 1+count)
			r.B = msgBytes
			err = c.${fieldName}[0].UnmarshalCanotoFrom(r)
			r.B = remainingBytes
			if err != nil {
				return err
			}

			for i := range count {
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]
				r.Unsafe = true
				err := canoto.ReadBytes(r, &msgBytes)
				r.Unsafe = originalUnsafe
				if err != nil {
					return err
				}

				remainingBytes := r.B
				r.B = msgBytes
				err = c.${fieldName}[1+i].UnmarshalCanotoFrom(r)
				r.B = remainingBytes
				if err != nil {
					return err
				}
			}
`,
			fixedRepeated: `		case ${fieldNumber}:
			if wireType != canoto.Len {
				return canoto.ErrUnexpectedWireType
			}

			originalUnsafe := r.Unsafe
			r.Unsafe = true
			var msgBytes []byte
			err := canoto.ReadBytes(r, &msgBytes)
			r.Unsafe = originalUnsafe
			if err != nil {
				return err
			}

			remainingBytes := r.B
			r.B = msgBytes
			err = c.${fieldName}[0].UnmarshalCanotoFrom(r)
			r.B = remainingBytes
			if err != nil {
				return err
			}

			isZero := len(msgBytes) == 0
			const numToRead = uint(len(c.${fieldName}) - 1)
			for i := range numToRead {
				if !canoto.HasPrefix(r.B, canoto__${escapedStructName}__${escapedFieldName}__tag) {
					return canoto.ErrUnknownField
				}
				r.B = r.B[len(canoto__${escapedStructName}__${escapedFieldName}__tag):]
				r.Unsafe = true
				err := canoto.ReadBytes(r, &msgBytes)
				r.Unsafe = originalUnsafe
				if err != nil {
					return err
				}

				remainingBytes := r.B
				r.B = msgBytes
				err = c.${fieldName}[1+i].UnmarshalCanotoFrom(r)
				r.B = remainingBytes
				if err != nil {
					return err
				}
				isZero = isZero && len(msgBytes) == 0
			}
			if isZero {
				return canoto.ErrZeroValue
			}
`,
		},
	})
}

func makeValid(m message) string {
	const (
		stringTemplate = `	if !utf8.ValidString(string(c.${fieldName})) {
		return false
	}
`
		repeatedStringTemplate = `	for _, v := range c.${fieldName} {
		if !utf8.ValidString(string(v)) {
			return false
		}
	}
`
		fieldTemplate = `	if !c.${fieldName}.ValidCanoto() {
		return false
	}
`
		repeatedFieldTemplate = `	for i := range c.${fieldName} {
		if !c.${fieldName}[i].ValidCanoto() {
			return false
		}
	}
`
	)
	var s strings.Builder
	for _, f := range m.fields {
		var template string
		switch f.canotoType {
		case canotoString:
			template = stringTemplate
		case canotoRepeatedString, canotoFixedRepeatedString:
			template = repeatedStringTemplate
		case canotoField:
			template = fieldTemplate
		case canotoRepeatedField, canotoFixedRepeatedField:
			template = repeatedFieldTemplate
		default:
			continue
		}
		_ = writeTemplate(&s, template, map[string]string{
			"fieldName": f.name,
		})
	}
	return s.String()
}

func makeSize(m message) string {
	const (
		fixedSizeTemplate = `	if !canoto.IsZero(c.${fieldName}) {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.Size${suffix}
	}
`
		repeatedFixedSizeTemplate = `	if num := len(c.${fieldName}); num != 0 {
		fieldSize := num * canoto.Size${suffix}
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(fieldSize)) + fieldSize
	}
`
		fixedRepeatedFixedSizeTemplate = `	if !canoto.IsZero(c.${fieldName}) {
		const fieldSize = len(c.${fieldName}) * canoto.Size${suffix}
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + fieldSize + canoto.SizeInt(int64(fieldSize))
	}
`
		bytesTemplate = `	if len(c.${fieldName}) != 0 {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(c.${fieldName})
	}
`
		repeatedBytesTemplate = `	for _, v := range c.${fieldName} {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(v)
	}
`
	)
	return writeMessage(m, messageTemplate{
		ints: typeTemplate{
			single: `	if !canoto.IsZero(c.${fieldName}) {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.Size${suffix}(c.${fieldName})
	}
`,
			repeated: `	if len(c.${fieldName}) != 0 {
		c.canotoData.${fieldName}Size = 0
		for _, v := range c.${fieldName} {
			c.canotoData.${fieldName}Size += canoto.Size${suffix}(v)
		}
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(c.canotoData.${fieldName}Size)) + c.canotoData.${fieldName}Size
	}
`,
			fixedRepeated: `	if !canoto.IsZero(c.${fieldName}) {
		c.canotoData.${fieldName}Size = 0
		for _, v := range c.${fieldName} {
			c.canotoData.${fieldName}Size += canoto.Size${suffix}(v)
		}
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(c.canotoData.${fieldName}Size)) + c.canotoData.${fieldName}Size
	}
`,
		},
		fints: typeTemplate{
			single:        fixedSizeTemplate,
			repeated:      repeatedFixedSizeTemplate,
			fixedRepeated: fixedRepeatedFixedSizeTemplate,
		},
		bools: typeTemplate{
			single:        fixedSizeTemplate,
			repeated:      repeatedFixedSizeTemplate,
			fixedRepeated: fixedRepeatedFixedSizeTemplate,
		},
		strings: typeTemplate{
			single:   bytesTemplate,
			repeated: repeatedBytesTemplate,
			fixedRepeated: `	if !canoto.IsZero(c.${fieldName}) {
		for _, v := range c.${fieldName} {
			c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(v)
		}
	}
`,
		},
		bytesTemplate:         bytesTemplate,
		repeatedBytesTemplate: repeatedBytesTemplate,
		fixedBytesTemplate: `	if !canoto.IsZero(c.${fieldName}) {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(c.${fieldName}[:])
	}
`,
		repeatedFixedBytesTemplate: `	if num := len(c.${fieldName}); num != 0 {
		fieldSize := len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(c.${fieldName}[0][:])
		c.canotoData.size += num * fieldSize
	}
`,
		fixedRepeatedBytesTemplate: `	{
		isZero := true
		for _, v := range c.${fieldName} {
			if len(v) != 0 {
				isZero = false
				break
			}
		}
		if !isZero {
			for _, v := range c.${fieldName} {
				c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(v)
			}
		}
	}
`,
		fixedRepeatedFixedBytesTemplate: `	if !canoto.IsZero(c.${fieldName}) {
		for i := range c.${fieldName} {
			c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeBytes(c.${fieldName}[i][:])
		}
	}
`,
		customs: typeTemplate{
			single: `	if fieldSize := c.${fieldName}.CalculateCanotoSize(); fieldSize != 0 {
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(fieldSize)) + fieldSize
	}
`,
			repeated: `	for i := range c.${fieldName} {
		fieldSize := c.${fieldName}[i].CalculateCanotoSize()
		c.canotoData.size += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(fieldSize)) + fieldSize
	}
`,
			fixedRepeated: `	{
		var (
			fieldSizeSum int
			totalSize    int
		)
		for i := range c.${fieldName} {
			fieldSize := c.${fieldName}[i].CalculateCanotoSize()
			fieldSizeSum += fieldSize
			totalSize += len(canoto__${escapedStructName}__${escapedFieldName}__tag) + canoto.SizeInt(int64(fieldSize)) + fieldSize
		}
		if fieldSizeSum != 0 {
			c.canotoData.size += totalSize
		}
	}
`,
		},
	})
}

func makeMarshal(m message) string {
	const (
		intTemplate = `	if !canoto.IsZero(c.${fieldName}) {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.Append${suffix}(w, c.${fieldName})
	}
`
		repeatedFintTemplate = `	if num := len(c.${fieldName}); num != 0 {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(num*canoto.Size${suffix}))
		for _, v := range c.${fieldName} {
			canoto.Append${suffix}(w, v)
		}
	}
`
		fixedRepeatedFintTemplate = `	if !canoto.IsZero(c.${fieldName}) {
		const fieldSize = len(c.${fieldName}) * canoto.Size${suffix}
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(fieldSize))
		for _, v := range c.${fieldName} {
			canoto.Append${suffix}(w, v)
		}
	}
`
		bytesTemplate = `	if len(c.${fieldName}) != 0 {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendBytes(w, c.${fieldName})
	}
`
		repeatedBytesTemplate = `	for _, v := range c.${fieldName} {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendBytes(w, v)
	}
`
	)
	return writeMessage(m, messageTemplate{
		ints: typeTemplate{
			single: intTemplate,
			repeated: `	if len(c.${fieldName}) != 0 {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(c.canotoData.${fieldName}Size))
		for _, v := range c.${fieldName} {
			canoto.Append${suffix}(w, v)
		}
	}
`,
			fixedRepeated: `	if !canoto.IsZero(c.${fieldName}) {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(c.canotoData.${fieldName}Size))
		for _, v := range c.${fieldName} {
			canoto.Append${suffix}(w, v)
		}
	}
`,
		},
		fints: typeTemplate{
			single:        intTemplate,
			repeated:      repeatedFintTemplate,
			fixedRepeated: fixedRepeatedFintTemplate,
		},
		bools: typeTemplate{
			single: `	if !canoto.IsZero(c.${fieldName}) {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendBool(w, true)
	}
`,
			repeated:      repeatedFintTemplate,
			fixedRepeated: fixedRepeatedFintTemplate,
		},
		strings: typeTemplate{
			single:   bytesTemplate,
			repeated: repeatedBytesTemplate,
			fixedRepeated: `	if !canoto.IsZero(c.${fieldName}) {
		for _, v := range c.${fieldName} {
			canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
			canoto.AppendBytes(w, v)
		}
	}
`,
		},
		bytesTemplate:         bytesTemplate,
		repeatedBytesTemplate: repeatedBytesTemplate,
		fixedBytesTemplate: `	if !canoto.IsZero(c.${fieldName}) {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendBytes(w, c.${fieldName}[:])
	}
`,
		repeatedFixedBytesTemplate: `	for i := range c.${fieldName} {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendBytes(w, c.${fieldName}[i][:])
	}
`,
		fixedRepeatedBytesTemplate: `	{
		isZero := true
		for _, v := range c.${fieldName} {
			if len(v) != 0 {
				isZero = false
				break
			}
		}
		if !isZero {
			for _, v := range c.${fieldName} {
				canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
				canoto.AppendBytes(w, v)
			}
		}
	}
`,
		fixedRepeatedFixedBytesTemplate: `	if !canoto.IsZero(c.${fieldName}) {
		for i := range c.${fieldName} {
			canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
			canoto.AppendBytes(w, c.${fieldName}[i][:])
		}
	}
`,
		customs: typeTemplate{
			single: `	if fieldSize := c.${fieldName}.CachedCanotoSize(); fieldSize != 0 {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(fieldSize))
		c.${fieldName}.MarshalCanotoInto(w)
	}
`,
			repeated: `	for i := range c.${fieldName} {
		canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
		canoto.AppendInt(w, int64(c.${fieldName}[i].CachedCanotoSize()))
		c.${fieldName}[i].MarshalCanotoInto(w)
	}
`,
			fixedRepeated: `	{
		isZero := true
		for i := range c.${fieldName} {
			if c.${fieldName}[i].CachedCanotoSize() != 0 {
				isZero = false
				break
			}
		}
		if !isZero {
			for i := range c.${fieldName} {
				canoto.Append(w, canoto__${escapedStructName}__${escapedFieldName}__tag)
				canoto.AppendInt(w, int64(c.${fieldName}[i].CachedCanotoSize()))
				c.${fieldName}[i].MarshalCanotoInto(w)
			}
		}
	}
`,
		},
	})
}

type messageTemplate struct {
	ints    typeTemplate
	fints   typeTemplate
	bools   typeTemplate
	strings typeTemplate

	bytesTemplate                   string
	repeatedBytesTemplate           string
	fixedBytesTemplate              string
	repeatedFixedBytesTemplate      string
	fixedRepeatedBytesTemplate      string
	fixedRepeatedFixedBytesTemplate string

	customs typeTemplate
}

type typeTemplate struct {
	single        string
	repeated      string
	fixedRepeated string
}

func writeMessage(m message, t messageTemplate) string {
	var s strings.Builder
	for _, f := range m.fields {
		var template string
		switch c := f.canotoType; c {
		case canotoInt, canotoSint:
			template = t.ints.single
		case canotoRepeatedInt, canotoRepeatedSint:
			template = t.ints.repeated
		case canotoFixedRepeatedInt, canotoFixedRepeatedSint:
			template = t.ints.fixedRepeated
		case canotoFint32, canotoFint64:
			template = t.fints.single
		case canotoRepeatedFint32, canotoRepeatedFint64:
			template = t.fints.repeated
		case canotoFixedRepeatedFint32, canotoFixedRepeatedFint64:
			template = t.fints.fixedRepeated
		case canotoBool:
			template = t.bools.single
		case canotoRepeatedBool:
			template = t.bools.repeated
		case canotoFixedRepeatedBool:
			template = t.bools.fixedRepeated
		case canotoString:
			template = t.strings.single
		case canotoRepeatedString:
			template = t.strings.repeated
		case canotoFixedRepeatedString:
			template = t.strings.fixedRepeated
		case canotoBytes:
			template = t.bytesTemplate
		case canotoFixedBytes:
			template = t.fixedBytesTemplate
		case canotoRepeatedBytes:
			template = t.repeatedBytesTemplate
		case canotoRepeatedFixedBytes:
			template = t.repeatedFixedBytesTemplate
		case canotoFixedRepeatedBytes:
			template = t.fixedRepeatedBytesTemplate
		case canotoFixedRepeatedFixedBytes:
			template = t.fixedRepeatedFixedBytesTemplate
		case canotoField:
			template = t.customs.single
		case canotoRepeatedField:
			template = t.customs.repeated
		default:
			template = t.customs.fixedRepeated
		}
		_ = writeTemplate(&s, template, f.templateArgs)
	}
	return s.String()
}

func writeTemplate(w io.Writer, template string, args map[string]string) error {
	s := os.Expand(template, func(key string) string {
		return args[key]
	})
	_, err := w.Write([]byte(s))
	return err
}