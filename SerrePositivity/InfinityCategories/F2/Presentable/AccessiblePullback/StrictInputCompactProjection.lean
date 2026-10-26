module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputCompactGluing

/-!
概要：厳密に貼った全入力付き頂点の compact 性を両成分で検出する。
方針：全 coslice 値の等式から元の二重基底射影の等式を回収する。
規約：元の全図式と先端を取り替えない。
使われ方：追加入力を保持する比較の厳密な貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：全二成分の値が compact な入力付き頂点に一致すれば元の貼り合わせの先端も compact。
方針：元の二重基底射影の可換性を各成分で適用する。
規約：同じ貼り合わせ頂点の全値を用いる。
使われ方：追加入力を忘れて貼った元の余錐の compact 性。 -/
lemma inputVertex_componentCompact_of_val_eqs
    {E D B K : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (μ : Cardinal.{u}) (p : E ⟶ B) (q : D ⟶ B)
    (a : K ⟶ pullback p q) (z : JoinCocone a)
    (v : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder a)).symm z)) _⦋0⦌)
    (cE : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (a ≫ pullback.fst p q))).symm
      (mapJoinCocone (pullback.fst p q) z))) _⦋0⦌)
    (cD : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (a ≫ pullback.snd p q))).symm
      (mapJoinCocone (pullback.snd p q) z))) _⦋0⦌)
    (hf : v.val ≫ sliceUnderPostcomp a (pullback.fst p q) = cE.val)
    (hg : v.val ≫ sliceUnderPostcomp a (pullback.snd p q) = cD.val)
    (hcE : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (a ≫ pullback.fst p q))).symm
        (mapJoinCocone (pullback.fst p q) z)) ≫
          sliceUnderProjection (a ≫ pullback.fst p q)).app (Opposite.op ⦋0⦌) cE))
    (hcD : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (a ≫ pullback.snd p q))).symm
        (mapJoinCocone (pullback.snd p q) z)) ≫
          sliceUnderProjection (a ≫ pullback.snd p q)).app (Opposite.op ⦋0⦌) cD)) :
    ComponentCompactVertex μ p q
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder a)).symm z) ≫
        sliceUnderProjection a).app (Opposite.op ⦋0⦌) v) := by
  constructor
  · have htip := inputVertex_base_projection_of_val_eq a (pullback.fst p q) z v cE hf
    change _ = (pullback.fst p q).app (Opposite.op ⦋0⦌)
      ((sliceOverProjection _ ≫ sliceUnderProjection a).app (Opposite.op ⦋0⦌) v) at htip
    rw [← htip]
    exact hcE
  · have htip := inputVertex_base_projection_of_val_eq a (pullback.snd p q) z v cD hg
    change _ = (pullback.snd p q).app (Opposite.op ⦋0⦌)
      ((sliceOverProjection _ ≫ sliceUnderProjection a).app (Opposite.op ⦋0⦌) v) at htip
    rw [← htip]
    exact hcD

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
