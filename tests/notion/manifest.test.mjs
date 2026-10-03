import test from "node:test";
import assert from "node:assert/strict";
import { candidateTargetsAtLine, itemAtLine, resolveItem, scopeTargetsAtLine } from "../../notion/lib/manifest.mjs";

const manifest = {
  items: {
    a: {id:"a",file:"A.lean",startLine:10,endLine:20,primaryDeclaration:"Foo.demo",displayKind:"theorem"},
    b: {id:"b",file:"A.lean",startLine:30,endLine:35,primaryDeclaration:"Foo.other",displayKind:"def"},
    c: {id:"c",file:"B.lean",startLine:5,endLine:8,primaryDeclaration:"Bar.demo",displayKind:"theorem"}
  },
  declarations: {"Foo.demo":"a","Foo.other":"b","Bar.demo":"c"},
  shortNames: {demo:["a","c"],other:["b"]},
  files: {"A.lean":["a","b"],"B.lean":["c"]},
  scopeTargets: {
    s1: {id:"s1",file:"A.lean",kind:"section",primaryDeclaration:"S",startLine:1,endLine:25},
    n1: {id:"n1",file:"A.lean",kind:"namespace",primaryDeclaration:"Foo",startLine:1,endLine:40},
    s2: {id:"s2",file:"A.lean",kind:"section",primaryDeclaration:"S",startLine:50,endLine:60}
  },
  legacyTargets: {"A.lean\u001fsection\u001fLegacy":{id:"legacy",file:"A.lean",startLine:1,endLine:40}}
};

test("resolveItem resolves full declarations", () => {
  assert.equal(resolveItem(manifest, new URLSearchParams("decl=Foo.demo")).id, "a");
});

test("resolveItem disambiguates short names with file", () => {
  assert.equal(resolveItem(manifest, new URLSearchParams("decl=demo&file=B.lean")).id, "c");
});

test("itemAtLine chooses containing item and previous fallback", () => {
  assert.equal(itemAtLine(manifest, "A.lean", 12).id, "a");
  assert.equal(itemAtLine(manifest, "A.lean", 28).id, "a");
});

test("scope targets are first-class and ordered from inner to outer", () => {
  assert.deepEqual(scopeTargetsAtLine(manifest, "A.lean", 12).map(x => x.id), ["s1","n1"]);
  assert.equal(resolveItem(manifest, new URLSearchParams("section=S&file=A.lean&line=1")).id, "s1");
});

test("candidateTargetsAtLine returns declaration, scopes, and selected item", () => {
  const targets = candidateTargetsAtLine(manifest, "A.lean", 12);
  assert.equal(targets.declarations[0].id, "a");
  assert.deepEqual(targets.scopes.map(x => x.id), ["s1","n1"]);
  assert.equal(targets.item.id, "a");
});

test("resolveItem preserves legacy section URLs", () => {
  assert.equal(resolveItem(manifest, new URLSearchParams("section=Legacy&file=A.lean")).id, "legacy");
});
