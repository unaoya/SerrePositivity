module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionChainMap

/-! # 実閉射による後合成の全次数成分

概要：標準豊穣後合成を元の dg 斉次合成で計算する。
方針：右単位テンソルの成分と閉零射の単位からの評価を使う。
規約：前三角性や小ささは不要。使われ方：AW 合成と実閉後合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
/-- 閉零射の豊穣後合成の全整数次数の成分式。 -/
lemma dgClosedPostcomposition_f {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    (k : ℤ) (a : GradedHom A x y k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s).f k a =
      compose A (closedHomEquiv A D _ _ s).val a (add_zero k) := by
  change ((rightUnitor' (homObject A D x y)).inv k ≫
    (homObject A D x y ◁ ForgetEnrichment.homTo (Complex A) s).f k ≫
      (eComp (Complex A) x y z).f k) a = _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  change forward A a (closedHomEquiv A D _ _ s).val (add_zero k) = _
  simp only [compose, mul_zero, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
