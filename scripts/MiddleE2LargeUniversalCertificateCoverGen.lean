module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateCover
meta import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateCover

/-!
# Generator of the middle-E2 large-atom cover

Untrusted generator for the large-atom middle-E2 cover certificate.

Input: the checker `leafOK` and the box splitting of
`MiddleE2LargeUniversalCertificateChecker`. Output: the cover shards
`.lake/cover-shards/MiddleE2LargeUniversalCertificateCoverShard*.lean`, whose
declarations `t0, t1, …` close every box of the search tree below `IBox.root`,
a leaf by `decide +kernel` and an internal box by `cover_of_split`. The shards
are intermediate files and are not built. `scripts/split_cover_certificate.py`
rewrites their declarations as the `MiddleE2LargeUniversalCertificatePiece*`
and `MiddleE2LargeUniversalCertificateRoot` modules. The generator only
chooses which literal boxes become kernel-evaluated leaves and writes their
statements; Lean proves every generated statement. No proof imports this file.
Run both from the repository root; the second command compares the split
modules with the library, byte for byte:

    lake env lean scripts/MiddleE2LargeUniversalCertificateCoverGen.lean
    python3 scripts/split_cover_certificate.py --check
-/

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint.CoverGen

open Erdos1017.MiddleE2LargeUniversal.FixedPoint

/-- The search tree of `cover`, with subtree node counts. -/
inductive T where
  | leaf
  | node (size : ℕ) (l r : T)

meta def T.size : T → ℕ
  | .leaf => 1
  | .node s _ _ => s

meta def build : ℕ → IBox → Option T
  | d, B =>
    if leafOK B then some .leaf
    else match d with
      | 0 => none
      | d + 1 => do
        let l ← build d B.split.1
        let r ← build d B.split.2
        return .node (l.size + r.size + 1) l r

meta def lit (B : IBox) : String :=
  s!"(IBox.mk {B.iq} {B.kq} {B.iA} {B.kA} {B.ib} {B.kb} {B.iu} {B.ku})"

/-- One generated declaration: its text and its kernel-evaluated node count. -/
structure Decl where
  text : String
  nodes : ℕ

/-- Post-order emission; returns the index of the declaration for `B`. -/
meta partial def emit (budget : ℕ) (d : ℕ) (B : IBox) (t : T) :
    StateM (Array Decl) ℕ := do
  match t with
  | .node s l r =>
    if budget < s then
      let i ← emit budget (d - 1) B.split.1 l
      let j ← emit budget (d - 1) B.split.2 r
      let k := (← get).size
      modify (·.push ⟨s!"theorem t{k} : cover {d} {lit B} = true :=\n  cover_of_split t{i} t{j}\n\n", 0⟩)
      return k
    else leafDecl d B s
  | .leaf => leafDecl d B 1
where
  leafDecl (d : ℕ) (B : IBox) (s : ℕ) : StateM (Array Decl) ℕ := do
    let k := (← get).size
    modify (·.push ⟨s!"theorem t{k} : cover {d} {lit B} = true := by decide +kernel\n\n", s⟩)
    return k

meta def header (k : ℕ) : String :=
  "module\n\n" ++
  (if k = 0 then "public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateCover\n"
    else s!"public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateCoverShard{k - 1}\n") ++
  "\n@[expose] public section\n\n" ++
  s!"/-! Generated cover shard {k}: literal boxes closed by bounded kernel evaluation\n" ++
  "or composed from their two literal halves. -/\n\n" ++
  "namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cov\n\n" ++
  "open Erdos1017.MiddleE2LargeUniversal.FixedPoint\n\n"

meta def generate (budget fileBudget : ℕ) : IO Unit := do
  let some t := build 80 IBox.root | IO.println "build failed"
  let ((), decls) := (do let _ ← emit budget 80 IBox.root t; pure ()).run #[]
  let mut files : Array String := #[]
  let mut cur := header 0
  let mut curN := 0
  for dcl in decls do
    if fileBudget < curN + dcl.nodes then
      files := files.push (cur ++ "end Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cov\n")
      cur := header files.size
      curN := 0
    cur := cur ++ dcl.text
    curN := curN + dcl.nodes
  files := files.push (cur ++ "end Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cov\n")
  IO.FS.createDirAll ".lake/cover-shards"
  for k in [0:files.size] do
    IO.FS.writeFile s!".lake/cover-shards/MiddleE2LargeUniversalCertificateCoverShard{k}.lean" files[k]!
  let leaves := decls.foldl (fun n d => if d.nodes = 0 then n else n + 1) 0
  let mx := decls.foldl (fun n d => max n d.nodes) 0
  IO.println s!"nodes {t.size} decls {decls.size} leaves {leaves} maxLeaf {mx} files {files.size} last t{decls.size - 1}"

#eval generate 40 30000

end Erdos1017.MiddleE2LargeUniversal.FixedPoint.CoverGen
