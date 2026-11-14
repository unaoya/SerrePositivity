module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.MooreZeroHomology
/-!
概要：実 π₀ と正規化 Moore H₀ の自然な全単射。
方針：実辺・正規化の包含・標準ホモロジー射の可換式を使う。
規約：元の正規化射を保持する。使われ方：β5(g) の弱同値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite HomologicalComplex
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
def modulePiZeroMooreEquiv (W : SimplicialObject (ModuleCat.{v} S)) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) ≃
      ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homology 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroBoundaryEquiv W).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso W).symm.toLinearEquiv.toEquiv
lemma modulePiZeroMooreEquiv_homologyBoundary (W : SimplicialObject (ModuleCat.{v} S))
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso W).hom.hom (modulePiZeroMooreEquiv W z) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroBoundaryEquiv W z :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso W).inv_hom_id_apply _
lemma modulePiZeroMooreEquiv_naturality (f : W ⟶ V)
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)) :
    modulePiZeroMooreEquiv V (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) z) =
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
        0).hom (modulePiZeroMooreEquiv W z) := by
  apply (ModuleCat.mono_iff_injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso V).hom).mp inferInstance
  rw [modulePiZeroMooreEquiv_homologyBoundary, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroBoundaryEquiv_naturality]
  have h := congrArg (fun ψ ↦ ψ.hom (modulePiZeroMooreEquiv W z))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso_naturality f)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso V).hom.hom
    ((HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
      0).hom (modulePiZeroMooreEquiv W z)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryQuotientMap f
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreZeroHomologyIso W).hom.hom (modulePiZeroMooreEquiv W z)) at h
  rw [modulePiZeroMooreEquiv_homologyBoundary] at h
  exact h.symm
lemma modulePiZeroMap_bijective_iff_homologyMap (f : W ⟶ V) :
    Function.Bijective (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)) ↔
    Function.Bijective
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
        0).hom := by
  have h := funext (modulePiZeroMooreEquiv_naturality f)
  exact ((modulePiZeroMooreEquiv V).comp_bijective _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective h)).trans
      ((modulePiZeroMooreEquiv W).bijective_comp _))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
