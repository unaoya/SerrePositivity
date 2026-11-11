module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedAtMaxImage
public import SerrePositivity.EInfinity.ComplexLimits.ComplexPostcomposeGraded

/-!
概要：選択 cochain と元の終端尾の閉射の実合成を、同じ普遍成分へ回収する。
方針：元の dg 合成を Hom 後合成へ戻し、符号作用と元の実像の式を使う。
規約：同じ閉射・次数・符号を保つ。使われ方：cone の最後に残る切断合成の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_compose {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
      ((normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last (J.max' hJ))))))).val
      (r • normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) (add_zero k) =
    r • (normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk := by
  rw [complexPostcompose_graded]
  have hs : (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (r • normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) =
    r • (homPostcompose X ((normalizedTensorElementDiagram A X Y).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) := by
    simp only [Units.smul_def, map_zsmul]
  exact hs.trans (congrArg (fun v => r • v)
    (normalizedTensorElementSelectedCochainAtMax_image A X Y c J k hJ hk))

end SerrePositivity.EInfinity.ComplexLimits
