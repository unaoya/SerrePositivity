module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityRightAxisConeComparison
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
/-!
概要：恒等右軸の元 cone 回収同型を、同じ実 perfect 加群の native nerve 内へ戻す。
方針：元の全包含への後合成で構成した全比較を、全 Hom の充満忠実性で反映する。
規約：同じ cone・Yoneda を保持。使われ方：固定 ν cone 比較の試験圏。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
local notation "I" => DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
local notation "J" => dgGluingRightAxis R C C M z hz
attribute [local irreducible] dgHomGluingBimodule

def dgGluingIdentityRightAxisPerfectConeIso : FunctorIso
    (dgNerve.map (dgPerfectYoneda R C))
    (dgNerve.map ((J).comp (dgHomGluingConeFunctor R C C C I I))) := by
  have hi : IsFullyFaithful (dgNerve.map (perfectDGModuleInclusion R C Set.univ)) :=
    dgNerve_map_isFullyFaithful_of_homIso _ (fun _ _ => by change IsIso (𝟙 _); infer_instance)
  apply hi.preimageFunctorIso
  rw [← dgNerve.map_comp, dgPerfectYoneda_inclusion, ← dgNerve.map_comp]
  change FunctorIso (dgNerve.map (dgYoneda R C))
    (dgNerve.map ((J).comp (dgHomGluingModuleConeFunctor R C C C I I)))
  exact dgGluingIdentityRightAxisConeModuleIso R C z hz

end SerrePositivity.InfinityCategories
