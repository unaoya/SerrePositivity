module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionComponents

/-!
# 元の豊穣前合成の全成分を小ささ仮定なしに計算する

概要：元の閉射の eHomWhiskerRight の成分は同じ斉次前合成である。
方針：左単位テンソルと元の閉零元の評価を直接計算する。
規約：Yoneda 加群による別の前合成や Small の入力を使わない。
使われ方：全複体 dg nerve の標準単位の全区間族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eHomWhiskerRight_compose_f {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (k : ℤ) (a : GradedHom A y z k) :
    (eHomWhiskerRight (Complex A) s (ForgetEnrichment.of (Complex A) z)).f k a =
      compose A a (closedHomEquiv A D _ _ s).val (zero_add k) := by
  change ((leftUnitor' (homObject A D y z)).inv k ≫
    (ForgetEnrichment.homTo (Complex A) s ▷ homObject A D y z).f k ≫
      (eComp (Complex A) x y z).f k) a = _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc]
  change forward A (closedHomEquiv A D _ _ s).val a (zero_add k) = _
  simp only [compose, zero_mul, Int.negOnePow_zero, one_smul]

end SerrePositivity.EInfinity.ComplexLimits
