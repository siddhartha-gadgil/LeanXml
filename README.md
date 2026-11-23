# LeanXml

XML support for Lean. This was removed from Lean core as it was not needed upstream. I have copied the code here for use by myself and others.

## Writing XML

`Lean.Xml.Element.toXml` (in `LeanXml/Serializer.lean`) writes an `Element` as well-formed XML 1.0: character data and attribute values are escaped, and `Lean.Xml.parse` reads the result back to the same tree. It returns a `SerializeError` for a tree XML cannot represent: a name that is not an XML name, a character outside the XML character range, or a comment that contains `--`, ends with `-` or holds a carriage return. `toString` on an `Element` is unchanged and escapes nothing.

## Namespaces

The parser is not namespace-aware: an `Element` has the names written in the document, and
`xmlns` declarations are ordinary attributes. `LeanXml.Namespace` resolves them per
[Namespaces in XML 1.0](https://www.w3.org/TR/xml-names/):

```lean
open Lean.Xml in
#eval do
  let root ← parseResolved "<t:a xmlns:t='urn:u' xml:lang='en'/>"
  return (root.is (some "urn:u") "a", root.attribute? (some xmlNamespace) "lang")
-- Except.ok (true, some "en")
```

Tests are in `LeanXmlTest/` and run with `lake test` (and with `lake build`).
