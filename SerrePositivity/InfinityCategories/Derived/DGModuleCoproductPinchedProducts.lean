module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCoproductHomDegrees
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearProductCriterion
/-!
概要：加群余積の同じ包含による制限は、全 pinched 線形単体の直積表示を与える。
方針：全 Hom の次数別直積同型を線形単体の一般判定へ渡す。
規約：元の加群・包含・全次数を保持し、射影性や compact 性は仮定しない。
使われ方：D-8 c5 の native 余積の写像空間検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve.PinchedHom
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {J : Type u}

lemma dgModuleCoproductHomProjections_bijective (M : J → ModuleCategory R D)
    (N : ModuleCategory R D) (k : ℤ) :
    Function.Bijective (fun z : (moduleCoproductHomFan R D M N).pt.X k =>
      fun j => (eHomWhiskerRight (Complex R) (Sigma.ι M j) N).f k z) := by
  have heq : (fun z : (moduleCoproductHomFan R D M N).pt.X k =>
      fun j => (eHomWhiskerRight (Complex R) (Sigma.ι M j) N).f k z) =
      fun z => (dgModuleCoproductHomDegreeIso R D M N k).hom z := by
    funext z j
    exact (ConcreteCategory.congr_hom (dgModuleCoproductHomDegreeIso_π R D M N k j) z).symm
  rw [heq]
  exact (dgModuleCoproductHomDegreeIso R D M N k).toLinearEquiv.bijective

lemma dgModuleCoproductPinchedLinear_bijective (M : J → ModuleCategory R D)
    (N : ModuleCategory R D) (n : ℕ) :
    Function.Bijective (fun s : LinearSimplex R
      (ForgetEnrichment.to (Complex R) (∐ M)) (ForgetEnrichment.to (Complex R) N) n =>
      fun j => pinchedLinearSimplexMap
        (eHomWhiskerRight (Complex R) (Sigma.ι M j) N) s) :=
  pinchedLinearSimplex_family_bijective _ (dgModuleCoproductHomProjections_bijective R D M N) n

lemma dgModuleCoproductStandard_bijective (M : J → ModuleCategory R D)
    (N : ModuleCategory R D) (n : ℕ) :
    Function.Bijective (fun s : DoldKanComparison.StandardSimplex R
      (ForgetEnrichment.to (Complex R) (∐ M)) (ForgetEnrichment.to (Complex R) N) n =>
      fun j => dgStandardSimplexMap
        (eHomWhiskerRight (Complex R) (Sigma.ι M j) N) s) :=
  dgStandardSimplex_family_bijective _ (dgModuleCoproductHomProjections_bijective R D M N) n

end SerrePositivity.InfinityCategories
