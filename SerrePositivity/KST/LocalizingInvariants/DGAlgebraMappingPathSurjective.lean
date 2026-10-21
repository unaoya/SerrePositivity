module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathGradedZero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：任意の実代数射の mapping-path target 評価は、各次数で全射となる。
方針：始点零・指定終点・比較零の斉次経路を、実 pullback に持ち上げる。
規約：斉次切断の微分保存は主張しない。使われ方：実全射因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

lemma gradedPullback (n : ℤ) :
    IsPullback ((inclusion R f).hom.f n) ((projection R f).hom.f n)
      ((Path.source R B).hom.f n) (f.hom.f n) :=
  Functor.map_isPullback (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
    (IsPullback.of_hasPullback (Path.source R B).hom f.hom)

lemma gradedSection_comm (n : ℤ) :
    ((biprod.inr : B.X ⟶ B.X ⊞ B.X).f n ≫ Path.gradedZero R B n) ≫
      (Path.source R B).hom.f n = (0 : B.X.X n ⟶ A.X.X n) ≫ f.hom.f n := by
  rw [Category.assoc, Path.gradedZero_source, ← HomologicalComplex.comp_f,
    biprod.inr_fst, HomologicalComplex.zero_f, zero_comp]

def gradedSection (n : ℤ) : B.X.X n ⟶ (algebra R f).X.X n :=
  (gradedPullback R f n).lift
    ((biprod.inr : B.X ⟶ B.X ⊞ B.X).f n ≫ Path.gradedZero R B n) 0
    (gradedSection_comm R f n)

lemma gradedSection_inclusion (n : ℤ) :
    gradedSection R f n ≫ (inclusion R f).hom.f n =
      (biprod.inr : B.X ⟶ B.X ⊞ B.X).f n ≫ Path.gradedZero R B n :=
  (gradedPullback R f n).lift_fst _ _ _

lemma gradedSection_target (n : ℤ) :
    gradedSection R f n ≫ (target R f).hom.f n = 𝟙 _ := by
  change gradedSection R f n ≫
    ((inclusion R f).hom.f n ≫ (Path.target R B).hom.f n) = _
  rw [← Category.assoc, gradedSection_inclusion, Category.assoc, Path.gradedZero_target,
    ← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]

lemma target_surjective (n : ℤ) : Function.Surjective ((target R f).hom.f n) := by
  intro y
  exact ⟨gradedSection R f n y, ConcreteCategory.congr_hom (gradedSection_target R f n) y⟩

lemma target_epi : Epi (target R f).hom := HomologicalComplex.epi_of_epi_f _
  (fun n => (ModuleCat.epi_iff_surjective _).2 (target_surjective R f n))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
