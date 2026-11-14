module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Fin.Basic

/-! # necklace の有限順序と joints
概要：両端を joints に含む有限順序集合で、necklace の骨格を表す。
方針：頂点を零から最後の頂点まで番号付けし、内部 joint を跨がない単体を使う。
規約：長さ零の点を単位として含む。使われ方：Rivera–Zeinalian 2018 §3 の実単体集合。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 零と最後の頂点を joints に持つ、有限 necklace の形。 -/
structure NecklaceShape where
  vertexMax : ℕ
  joints : Finset ℕ
  zero_mem : 0 ∈ joints
  last_mem : vertexMax ∈ joints
  mem_le : ∀ j ∈ joints, j ≤ vertexMax

namespace NecklaceShape


/-- 元の全頂点。 -/
abbrev Vertex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) := Fin (T.vertexMax + 1)

/-- 原典の立方体の次元は、joint ではない頂点の個数。 -/
def dimension (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : ℕ :=
  ((Finset.range (T.vertexMax + 1)).filter (fun j => j ∉ T.joints)).card

/-- 元の標準 n 単体一つからなる necklace。n=0 は点。 -/
def single (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape where
  vertexMax := n
  joints := {0, n}
  zero_mem := by simp
  last_mem := by simp
  mem_le j hj := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> omega

/-- 元の始頂点。 -/
def first (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.Vertex := 0

/-- 元の終頂点。 -/
def last (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.Vertex := Fin.last T.vertexMax

/-- 単体のどの二頂点の間にも joint が厳密に内部にはないという bead 条件。 -/
def Allows (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ} (s : Fin (n + 1) → T.Vertex) : Prop :=
  ∀ (i j : Fin (n + 1)) (k : ℕ), k ∈ T.joints → ¬ ((s i).val < k ∧ k < (s j).val)

/-- bead 条件は任意の頂点再添字付けに沿う制限で保存される。 -/
lemma allows_precomp (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {m n : ℕ} {s : Fin (n + 1) → T.Vertex}
    (hs : T.Allows s) (f : Fin (m + 1) → Fin (n + 1)) : T.Allows (s ∘ f) := by
  intro i j k hk
  exact hs (f i) (f j) k hk

/-- 定値な単体は元の necklace 内にある。 -/
lemma allows_const (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) (n : ℕ) :
    T.Allows (fun _ : Fin (n + 1) => v) := by
  intro i j k hk
  change ¬ (v.val < k ∧ k < v.val)
  omega

/-- 標準単体一つでは、すべての頂点列が bead 条件を満たす。 -/
lemma single_allows (n m : ℕ) (s : Fin (m + 1) → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).Allows s := by
  intro i j k hk h
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton] at hk
  change (s i).val < k ∧ k < (s j).val at h
  have hj : (s j).val < n + 1 := (s j).isLt
  rcases hk with hk | hk <;> omega

/-- 単調な単体の bead 条件は、元の最初と最後の頂点だけで判定できる。 -/
lemma allows_iff_endpoints (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : Fin (n + 1) →o T.Vertex) :
    T.Allows s ↔ ∀ k ∈ T.joints, ¬ ((s 0).val < k ∧ k < (s (Fin.last n)).val) := by
  constructor
  · intro h k hk
    exact h 0 (Fin.last n) k hk
  · intro h i j k hk hi
    have h0 : (s 0).val ≤ (s i).val := s.monotone (Fin.zero_le i)
    have h1 : (s j).val ≤ (s (Fin.last n)).val := s.monotone (Fin.le_last j)
    exact h k hk ⟨lt_of_le_of_lt h0 hi.1, lt_of_lt_of_le hi.2 h1⟩

end NecklaceShape
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.Allows (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.Allows := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.Allows

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.Vertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.Vertex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.Vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.allows_const := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.allows_const

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.allows_iff_endpoints := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.allows_iff_endpoints

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.allows_precomp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.allows_precomp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.dimension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.dimension := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.dimension

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.first (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.first

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.joints (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.joints := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.joints

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.last (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.last_mem := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.last_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mem_le := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mem_le

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.recOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single_allows := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single_allows

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexMax (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.vertexMax := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexMax

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.zero_mem := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.zero_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.first._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.first._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single.eq_1
