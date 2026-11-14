module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementSelectedCochain
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.NerveInclusionSimplex

/-!
概要：実 cone の対象族と、元の frame 図式の同じ通常単体を構成する。
方針：始点に X を加え、他の頂点では元の閉 nerve の成分を使う。
規約：元の frame 射と対象を保持する。使われ方：混合 cochain との実単体データの接合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

def coneTailOrderHom (n : ℕ) : Fin (n + 2) →o Fin (n + 1) where
  toFun i := ⟨i.val - 1, by omega⟩
  monotone' i j hij := Nat.sub_le_sub_right hij 1

lemma coneTailOrderHom_succ {n : ℕ} (i : Fin (n + 1)) : coneTailOrderHom n i.succ = i := by
  apply Fin.ext
  simp [coneTailOrderHom]

variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeObj {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) : Fin (n + 2) → Complex A :=
  Fin.cases X (fun i => (normalizedTensorElementDiagram A X Y).obj (c.obj i))

lemma normalizedTensorConeObj_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    normalizedTensorConeObj A X Y c 0 = X := rfl

lemma normalizedTensorConeObj_succ {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    normalizedTensorConeObj A X Y c i.succ =
      (normalizedTensorElementDiagram A X Y).obj (c.obj i) := rfl

lemma normalizedTensorConeObj_ne_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    normalizedTensorConeObj A X Y c i =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (coneTailOrderHom n i)) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [normalizedTensorConeObj_succ, coneTailOrderHom_succ]

def normalizedTensorConeOrdinarySimplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((coneTailOrderHom n).monotone.functor ⋙ c ⋙
    normalizedTensorElementDiagram A X Y ⋙ complexToClosed A)

lemma normalizedTensorConeOrdinarySimplex_obj {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (i : Fin (n + 2)) :
    (normalizedTensorConeOrdinarySimplex A X Y c).obj i =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (coneTailOrderHom n i)) := rfl

end SerrePositivity.EInfinity.ComplexLimits
