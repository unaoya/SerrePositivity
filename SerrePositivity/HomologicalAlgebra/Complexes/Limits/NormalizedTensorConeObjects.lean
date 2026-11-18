module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementSelectedCochain
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

def coneTailOrderHom (n : ℕ) : Fin (n + 2) →o Fin (n + 1) where
  toFun i := ⟨i.val - 1, by omega⟩
  monotone' i j hij := Nat.sub_le_sub_right hij 1

lemma coneTailOrderHom_succ {n : ℕ} (i : Fin (n + 1)) : _root_.SerrePositivity.ComplexLimits.coneTailOrderHom n i.succ = i := by
  apply Fin.ext
  simp [_root_.SerrePositivity.ComplexLimits.coneTailOrderHom]

variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeObj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) : Fin (n + 2) → Complex A :=
  Fin.cases X (fun i => (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i))

lemma normalizedTensorConeObj_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c 0 = X := rfl

lemma normalizedTensorConeObj_succ {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c i.succ =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i) := rfl

lemma normalizedTensorConeObj_ne_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c i =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n i)) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ, _root_.SerrePositivity.ComplexLimits.coneTailOrderHom_succ]

def normalizedTensorConeOrdinarySimplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n).monotone.functor ⋙ c ⋙
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)

lemma normalizedTensorConeOrdinarySimplex_obj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 2)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeOrdinarySimplex A X Y c).obj i =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom n i)) := rfl

end SerrePositivity.ComplexLimits
