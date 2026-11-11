module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # 閉零射の豊穣前後合成の全次数成分
概要：閉零射による豊穣前後合成は、元の通常順斉次合成と一致する。
方針：左右単位テンソルの純粋元を評価し、零次数の Koszul 符号を消す。
規約：対象の小ささを要求しない。使われ方：全 Hom 自然比較の標準 DK 移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y z : D}

/-- 閉零射による豊穣後合成は、各整数次数の元の斉次後合成。 -/
lemma dgClosedWhiskerLeft_f
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    (k : ℤ) (a : GradedHom A x y k) :
    (eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) x) s).f k a =
      compose A (closedHomEquiv A D _ _ s).val a (add_zero k) := by
  change ((rightUnitor' (homObject A D x y)).inv k ≫
    (homObject A D x y ◁ ForgetEnrichment.homTo (Complex A) s).f k ≫
      (eComp (Complex A) x y z).f k) a = _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc]
  change forward A a (closedHomEquiv A D _ _ s).val (add_zero k) = _
  simp only [compose, mul_zero, Int.negOnePow_zero, one_smul]

/-- 閉零射による豊穣前合成も、各整数次数の元の斉次前合成。 -/
lemma dgClosedWhiskerRight_f
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

end SerrePositivity.KST.SConstruction
