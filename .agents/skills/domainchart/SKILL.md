---
description: This skill visualizes the domain object hierarchy in the project using domainchart npm package.
metadata:
  github-path: skills/domainchart
  github-ref: refs/heads/main
  github-repo: https://github.com/kt3k/domainchart
  github-tree-sha: ca4b540ea091684b84b444bbacd87e18518b272d
name: domainchart
---

# domainchart

A skill for expressing a DDD domain as a **hierarchy of domain objects** that can be rendered as a
tree-style diagram. The focus is on modeling the structure correctly; the renderer is just a thin
step at the end.

## Scope (argument)

The skill takes an optional argument that names the **scope** to analyze — file paths, directory
paths, or a free-form description (e.g. "the billing module"). When no argument is given, treat the
**entire codebase** as the scope.

## Workflow

Execute the steps below in order. Do not skip ahead.

1. **Read the code in scope.** Carefully read every file under the given scope (or the whole
   repository if no argument was provided). Note classes, types, structs, schemas, and any data
   structures that look like domain concepts.
2. **List the domain objects.** Enumerate each candidate as either an Entity (identity-bearing,
   independent lifecycle — 🔷) or a Value Object (defined purely by its attributes, interchangeable
   when equal — 💎). IDs like `OrderId` / `UserId` are Value Objects. One node per concept; don't
   merge.
3. **Read `npx domainchart types`.** Run the command and read its JSON Schema output. This is the
   authoritative input shape — do not guess the schema from memory.
4. **Map the listed objects to that schema.** Produce a JSON document that conforms to the schema
   from step 3:
   - Use a child's `name` as the parent property's `type` to express the parent→child edge.
     Collections / optionals / unions all count as references: `OrderItem[]`, `Array<OrderItem>`,
     `Set<OrderItem>`, `OrderItem?`, `Foo | Bar`, `Array<Foo | Bar>`.
   - Any `type` that does not match a declared `name` is a primitive leaf (`string`, `number`,
     `Date`, …).
   - Pick aggregate roots intentionally — a root owns its children, and children should be reachable
     only through their root. Break cross-aggregate cycles by referencing the other root's ID, not
     the root itself.
5. **Save the JSON to a temp directory.** Create one with `mktemp -d` and write the document to
   `<tmp>/domainchart.json`. Do not write to the project yet.
6. **Validate.** Run `npx domainchart validate <tmp>/domainchart.json`. If any errors or warnings
   are reported, fix the JSON and re-run. **Repeat until the output is clean.**
7. **Build the HTML.** Run `npx domainchart build <tmp>/domainchart.json -o <tmp>/domainchart.html`.
8. **Open it in a browser** so the user can see the result (`open
   <tmp>/domainchart.html` on
   macOS).
9. **Ask whether to keep it.** Ask the user whether to copy `domainchart.json` and
   `domainchart.html` into the project, and where. Only copy if they confirm.

## Hierarchy design guidelines

- **One root per aggregate.** If two candidates both want to own the same child, decide which truly
  owns it; the other should reference it by ID (a Value Object like `OrderId`) instead of by object.
- **Break cross-aggregate cycles with ID references.** A direct object reference to
  `OtherAggregateRoot` creates a child edge; referencing its ID (`OtherAggregateRootId` as a Value
  Object) keeps the two aggregates separate.
- **Cycles with no clear root are rejected.** If the validator complains, the hierarchy is ambiguous
  — pick a root or break the cycle via an ID.
- **Depth follows ownership, not data flow.** Put a property under its owner, not under whoever
  happens to read it.

## Example

```json
{
  "title": "EC Site Domain Model",
  "models": [
    {
      "name": "Order",
      "kind": "entity",
      "description": "Order aggregate root",
      "properties": [
        { "name": "id", "type": "OrderId" },
        { "name": "items", "type": "OrderItem[]" },
        { "name": "customerId", "type": "CustomerId" }
      ]
    },
    {
      "name": "OrderItem",
      "kind": "entity",
      "properties": [
        { "name": "quantity", "type": "number" },
        { "name": "unitPrice", "type": "Money" }
      ]
    },
    {
      "name": "Money",
      "kind": "value_object",
      "properties": [
        { "name": "amount", "type": "number" },
        { "name": "currency", "type": "string" }
      ]
    },
    {
      "name": "OrderId",
      "kind": "value_object",
      "properties": [{ "name": "value", "type": "string" }]
    },
    {
      "name": "CustomerId",
      "kind": "value_object",
      "properties": [{ "name": "value", "type": "string" }]
    }
  ]
}
```

Inferred result: `Order` becomes the aggregate root, owning `OrderItem` (which owns `Money`) and
`OrderId`. `CustomerId` is a leaf — the `Customer` aggregate is referenced only by ID, keeping the
two aggregates separate.
