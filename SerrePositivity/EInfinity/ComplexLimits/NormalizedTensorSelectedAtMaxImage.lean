module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementSelectedCochain

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_image {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    (normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj i)) k),
      (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last j))))).f k
        (cast (congrArg (fun z => (GradedHom A X
          ((normalizedTensorElementDiagram A X Y).obj (c.obj z)) k : Type u)) h) v) =
      (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last i))))).f k v := by
    intro i j h v
    subst j
    rfl
  exact (ht _ _ (normalizedTensorElementSelection_last J hJ)
    (normalizedTensorElementSelectedCochain A X Y c J k hJ hk)).trans
      (normalizedTensorElementSelectedCochain_image A X Y c J k hJ hk)

end SerrePositivity.EInfinity.ComplexLimits
