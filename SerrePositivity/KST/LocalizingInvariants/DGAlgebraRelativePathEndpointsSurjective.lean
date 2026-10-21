module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathGradedPair

/-!
概要：相対二端点射は、任意の底の代数射に対して各次数で全射となる。
方針：零比較の斉次相対経路が、同じ二端点の実切断となることを証明する。
規約：斉次切断の微分保存は主張しない。使われ方：全射準同型の相対持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

lemma gradedZeroLift_source (n : ℤ) :
    gradedZeroLift R p n ≫ (source R p).hom.f n = (endpointsSource R p).hom.f n := by
  change gradedZeroLift R p n ≫
    ((inclusion R p).hom.f n ≫ (Path.source R C).hom.f n) = _
  rw [← Category.assoc, gradedZeroLift_inclusion, Category.assoc, Path.gradedZero_source,
    ← HomologicalComplex.comp_f]
  rw [pairHom_fst]

lemma gradedZeroLift_target (n : ℤ) :
    gradedZeroLift R p n ≫ (target R p).hom.f n = (endpointsTarget R p).hom.f n := by
  change gradedZeroLift R p n ≫
    ((inclusion R p).hom.f n ≫ (Path.target R C).hom.f n) = _
  rw [← Category.assoc, gradedZeroLift_inclusion, Category.assoc, Path.gradedZero_target,
    ← HomologicalComplex.comp_f]
  rw [pairHom_snd]

lemma gradedZeroLift_endpointsMap (n : ℤ) :
    gradedZeroLift R p n ≫ (endpointsMap R p).hom.f n = 𝟙 _ := by
  have hs : (endpointsMap R p).hom.f n ≫ (endpointsSource R p).hom.f n =
      (source R p).hom.f n :=
    congrArg (fun f => f.f n) (congrArg Mon.Hom.hom (endpointsMap_source R p))
  have ht : (endpointsMap R p).hom.f n ≫ (endpointsTarget R p).hom.f n =
      (target R p).hom.f n :=
    congrArg (fun f => f.f n) (congrArg Mon.Hom.hom (endpointsMap_target R p))
  apply (gradedEndpointsPullback R p n).hom_ext
  · rw [Category.assoc, hs, gradedZeroLift_source, Category.id_comp]
  · rw [Category.assoc, ht, gradedZeroLift_target, Category.id_comp]

lemma endpointsMap_surjective (n : ℤ) :
    Function.Surjective ((endpointsMap R p).hom.f n) := by
  intro y
  exact ⟨gradedZeroLift R p n y,
    ConcreteCategory.congr_hom (gradedZeroLift_endpointsMap R p n) y⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
