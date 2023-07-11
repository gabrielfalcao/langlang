package parsing

import (
	"fmt"
	"strings"
)

type Location struct {
	Line   int
	Column int
	Cursor int
}

func NewLocation(line, column, cursor int) Location {
	return Location{line, column, cursor}
}

func (l Location) String() string {
	return fmt.Sprintf("%d:%d", l.Line, l.Column)
}

type Span struct {
	Start Location
	End   Location
}

func NewSpan(s, e Location) Span {
	return Span{s, e}
}

func (s Span) String() string {
	if s.Start.Line == s.End.Line && s.Start.Line == 0 {
		return fmt.Sprintf("%d..%d", s.Start.Column, s.End.Column)
	}
	return fmt.Sprintf("%s..%s", s.Start, s.End)
}

// Node is the interface that defines all behavior needed by the values output by the parser
type Node interface {
	// Span returns the location span in which the node was found within the input text
	Span() Span

	// String returns the string representation of a given node
	String() string
}

// Node Type: Any

type AnyNode struct {
	span Span
}

func NewAnyNode(s Span) *AnyNode {
	n := &AnyNode{}
	n.span = s
	return n
}

func (n AnyNode) Span() Span { return n.span }

func (n AnyNode) String() string {
	return fmt.Sprintf("Any @ %s", n.Span())
}

// Node Type: Literal

type LiteralNode struct {
	span  Span
	Value string
}

func NewLiteralNode(v string, s Span) *LiteralNode {
	n := &LiteralNode{Value: v}
	n.span = s
	return n
}

func (n LiteralNode) Span() Span { return n.span }

func (n LiteralNode) String() string {
	return fmt.Sprintf("Literal(%s) @ %s", n.Value, n.Span())
}

// Node Type: Identifier

type IdentifierNode struct {
	span  Span
	Value string
}

func NewIdentifierNode(v string, s Span) *IdentifierNode {
	n := &IdentifierNode{Value: v}
	n.span = s
	return n
}

func (n IdentifierNode) Span() Span { return n.span }

func (n IdentifierNode) String() string {
	return fmt.Sprintf("Identifier(%s) @ %s", n.Value, n.Span())
}

// Node Type: Range

type RangeNode struct {
	span  Span
	Left  string
	Right string
}

func NewRangeNode(left, right string, s Span) *RangeNode {
	n := &RangeNode{Left: left, Right: right}
	n.span = s
	return n
}

func (n RangeNode) Span() Span { return n.span }

func (n RangeNode) String() string {
	return fmt.Sprintf("Range(%s, %s) @ %s", n.Left, n.Right, n.Span())
}

// Node Type: Class

type ClassNode struct {
	span  Span
	Items []Node
}

func NewClassNode(items []Node, s Span) *ClassNode {
	n := &ClassNode{Items: items}
	n.span = s
	return n
}

func (n ClassNode) Span() Span { return n.span }

func (n ClassNode) String() string {
	var (
		s  strings.Builder
		ln = len(n.Items) - 1
	)

	s.WriteString("Class(")

	for i, child := range n.Items {
		s.WriteString(child.String())

		if i < ln {
			s.WriteString(", ")
		}
	}

	s.WriteString(") @ ")
	s.WriteString(n.Span().String())

	return s.String()
}

// Node Type: Optional

type OptionalNode struct {
	span Span
	Expr Node
}

func NewOptionalNode(expr Node, s Span) *OptionalNode {
	n := &OptionalNode{Expr: expr}
	n.span = s
	return n
}

func (n OptionalNode) Span() Span { return n.span }

func (n OptionalNode) String() string {
	return fmt.Sprintf("Optional(%s) @ %s", n.Expr, n.Span())
}

// Node Type: ZeroOrMore

type ZeroOrMoreNode struct {
	span Span
	Expr Node
}

func NewZeroOrMoreNode(expr Node, s Span) *ZeroOrMoreNode {
	n := &ZeroOrMoreNode{Expr: expr}
	n.span = s
	return n
}

func (n ZeroOrMoreNode) Span() Span { return n.span }

func (n ZeroOrMoreNode) String() string {
	return fmt.Sprintf("ZeroOrMore(%s) @ %s", n.Expr, n.Span())
}

// Node Type: OneOrMore

type OneOrMoreNode struct {
	span Span
	Expr Node
}

func NewOneOrMoreNode(expr Node, s Span) *OneOrMoreNode {
	n := &OneOrMoreNode{Expr: expr}
	n.span = s
	return n
}

func (n OneOrMoreNode) Span() Span { return n.span }

func (n OneOrMoreNode) String() string {
	return fmt.Sprintf("OneOrMore(%s) @ %s", n.Expr, n.Span())
}

// Node Type: And

type AndNode struct {
	span Span
	Expr Node
}

func NewAndNode(expr Node, s Span) *AndNode {
	n := &AndNode{Expr: expr}
	n.span = s
	return n
}

func (n AndNode) Span() Span { return n.span }

func (n AndNode) String() string {
	return fmt.Sprintf("And(%s) @ %s", n.Expr, n.Span())
}

// Node Type: Not

type NotNode struct {
	span Span
	Expr Node
}

func NewNotNode(expr Node, s Span) *NotNode {
	n := &NotNode{Expr: expr}
	n.span = s
	return n
}

func (n NotNode) Span() Span { return n.span }

func (n NotNode) String() string {
	return fmt.Sprintf("Not(%s) @ %s", n.Expr, n.Span())
}

// Node Type: Sequence

type SequenceNode struct {
	span  Span
	Items []Node
}

func NewSequenceNode(items []Node, s Span) *SequenceNode {
	n := &SequenceNode{Items: items}
	n.span = s
	return n
}

func (n SequenceNode) Span() Span { return n.span }

func (n SequenceNode) String() string {
	var (
		s  strings.Builder
		ln = len(n.Items) - 1
	)

	s.WriteString("Sequence(")

	for i, child := range n.Items {
		s.WriteString(child.String())

		if i < ln {
			s.WriteString(", ")
		}
	}

	s.WriteString(") @ ")
	s.WriteString(n.Span().String())

	return s.String()
}

// Node Type: Choice

type ChoiceNode struct {
	span  Span
	Items []Node
}

func NewChoiceNode(items []Node, s Span) *ChoiceNode {
	n := &ChoiceNode{Items: items}
	n.span = s
	return n
}

func (n ChoiceNode) Span() Span { return n.span }

func (n ChoiceNode) String() string {
	var (
		s  strings.Builder
		ln = len(n.Items) - 1
	)

	s.WriteString("Choice(")

	for i, child := range n.Items {
		s.WriteString(child.String())

		if i < ln {
			s.WriteString(", ")
		}
	}

	s.WriteString(") @ ")
	s.WriteString(n.Span().String())

	return s.String()
}

// Node Type: Definition

type DefinitionNode struct {
	span Span
	Name string
	Expr Node
}

func NewDefinitionNode(name string, expr Node, s Span) *DefinitionNode {
	n := &DefinitionNode{Name: name, Expr: expr}
	n.span = s
	return n
}

func (n DefinitionNode) Span() Span { return n.span }

func (n DefinitionNode) String() string {
	return fmt.Sprintf("Definition[%s](%s) @ %s", n.Name, n.Expr, n.Span())
}

// Node Type: Grammar

type GrammarNode struct {
	span  Span
	Items []Node
}

func NewGrammarNode(items []Node, s Span) *GrammarNode {
	n := &GrammarNode{Items: items}
	n.span = s
	return n
}

func (n GrammarNode) Span() Span { return n.span }

func (n GrammarNode) String() string {
	var (
		s  strings.Builder
		ln = len(n.Items) - 1
	)

	s.WriteString("Grammar(")

	for i, child := range n.Items {
		s.WriteString(child.String())

		if i < ln {
			s.WriteString(", ")
		}
	}

	s.WriteString(") @ ")
	s.WriteString(n.Span().String())

	return s.String()
}
