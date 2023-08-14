package parser

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

//go:generate go run ../cmd -language go -grammar ./basic.peg -go-prefix Basic -output ./basic.go

func TestIsSyntactic(t *testing.T) {
	t.Run("sequence with literal terminals is always syntactic", func(t *testing.T) {
		// Matches without the spaces in the input
		p := newBasicParser("abc")
		v, err := p.ParseSyntactic0()
		require.NoError(t, err)
		assert.Equal(t, "abc", v.Text())

		// It doesn't expect spaces between the sequence items
		p = newBasicParser("a b c")
		_, err = p.ParseSyntactic0()
		require.Error(t, err)
		assert.Equal(t, "Missing `b` @ 1..2", err.Error())
	})

	t.Run("sequence with grammar nodes that are not terminals are not syntactic", func(t *testing.T) {
		// Optional spaces are introduced between the items
		// within the top-level sequence

		p := newBasicParser("abcabc!")
		v, err := p.ParseNotSyntactic0()
		require.NoError(t, err)
		assert.Equal(t, "abcabc!", v.Text())

		p = newBasicParser("abc abc !")
		v, err = p.ParseNotSyntactic0()
		require.NoError(t, err)
		assert.Equal(t, "abc abc !", v.Text())
	})

	t.Run("Lexification operator on a single item within a syntactic rule", func(t *testing.T) {
		p := newBasicParser("1st")
		v, err := p.ParseOrdinal()
		require.NoError(t, err)
		assert.Equal(t, "1st", v.Text())

		p = newBasicParser("1 st")
		_, err = p.ParseOrdinal()
		require.Error(t, err)
		assert.Equal(t, "ord @ 1", err.Error())
	})

	t.Run("Lexification operator on a sequence within a sequence", func(t *testing.T) {
		for _, test := range []string{
			"a9:30",
			"a999:99",
			"bb :12",
		} {
			p := newBasicParser(test)
			v, err := p.ParseSPC0()
			require.NoError(t, err)
			assert.Equal(t, test, v.Text())
		}

		for test, errMsg := range map[string]string{
			" a9:30":   "Expected `a-z`, `A-Z` but got ` ` @ 0",
			"a 999:99": "Expected `a-z`, `A-Z`, `0-9` but got ` ` @ 1",
			"a9: 30":   "Expected `0-9` but got ` ` @ 3",
		} {
			p := newBasicParser(test)
			_, err := p.ParseSPC0()
			require.Error(t, err, test)
			assert.Equal(t, errMsg, err.Error())
		}
	})

	t.Run("Variation of lexification operator on a sequence within a sequence", func(t *testing.T) {
		for _, test := range []string{
			"a9:30",
			"a 999:99",
			"a 999: 99",
		} {
			p := newBasicParser(test)
			v, err := p.ParseSPC1()
			require.NoError(t, err)
			assert.Equal(t, test, v.Text())
		}

		for test, errMsg := range map[string]string{
			" a9:30":    "Expected `a-z`, `A-Z` but got ` ` @ 0",
			"a 999 :99": "Missing `:` @ 5..6",
		} {
			p := newBasicParser(test)
			_, err := p.ParseSPC1()
			require.Error(t, err, test)
			assert.Equal(t, errMsg, err.Error())
		}
	})
}

func TestAnd(t *testing.T) {
	t.Run("all and uses match", func(t *testing.T) {
		for _, test := range []string{
			"#",
			"#*",
			"#***",
		} {
			p := newBasicParser(test)
			v, err := p.ParseHashWithAnAnd()
			require.NoError(t, err)
			assert.Equal(t, test, v.Text())
		}
	})

	t.Run("all and uses do not match", func(t *testing.T) {
		for test, errMsg := range map[string]string{
			"x":    "missingdot @ 0",
			"##":   "Expected EOF @ 1",
			"#**!": "Expected EOF @ 3",
		} {
			p := newBasicParser(test)
			p.SetLabelMessages(map[string]string{"eof": "Expected EOF"})
			_, err := p.ParseHashWithAnAnd()
			require.Error(t, err)
			assert.Equal(t, errMsg, err.Error())
		}
	})
}

func TestNullable(t *testing.T) {
	t.Run("matching will succeed but no input will be consumed", func(t *testing.T) {
		p := newBasicParser("c")
		v, err := p.ParseMaybeNull()
		require.NoError(t, err)
		assert.Nil(t, v)
	})
}

func newBasicParser(input string) *BasicParser {
	p := NewBasicParser()
	p.SetInput(input)
	return p
}
