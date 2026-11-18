module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementSelectedCochain

/-!
概要：最大点へ輸送した同じ選択 cochain の像を、元の列の同じ普遍成分に戻す。
方針：添字等式の輸送と後合成を両立させ、元の選択係数の像の定理を使う。
規約：元の最大点・終端尾・実 frame 射を保持する。
使われ方：実 cone の混合削除項と終端合成項の共通座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_image {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k),
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last j))))).f k
        (cast (congrArg (fun z => (GradedHom A X
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj z)) k : Type u)) h) v) =
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last i))))).f k v := by
    intro i j h v
    subst j
    rfl
  exact (ht _ _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection_last J hJ)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain A X Y c J k hJ hk)).trans
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain_image A X Y c J k hJ hk)

end SerrePositivity.ComplexLimits
