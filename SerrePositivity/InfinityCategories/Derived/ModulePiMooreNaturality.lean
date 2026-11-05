module
public import SerrePositivity.InfinityCategories.Derived.MooreHomologyNaturality
/-!
概要：正次数 π と同じ Moore ホモロジーの群同型の自然性。
方針：元の実射を保ち、包含・cycles・ホモロジー射の可換式を照合する。
規約：正次数は n+1。使われ方：β5(g) の単体の弱同値と準同型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma modulePiMooreGroupEquiv_homologySphere
    (W : SimplicialObject (ModuleCat.{v} S))
    [SSet.KanComplex (moduleUnderlyingSSet W)] (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet W) n 0) :
    (mooreHomologySphereIso W n).hom.hom (modulePiMooreGroupEquiv W n s) =
      modulePiSphereGroupEquiv W n s := by
  exact (mooreHomologySphereIso W n).inv_hom_id_apply _
lemma modulePiMooreGroupEquiv_naturality
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet W) n 0) :
    modulePiMooreGroupEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
        (moduleUnderlyingSSetMap_zero f) s) =
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
        (n + 1)).hom (modulePiMooreGroupEquiv W n s) := by
  apply (ModuleCat.mono_iff_injective (mooreHomologySphereIso V n).hom).mp inferInstance
  rw [modulePiMooreGroupEquiv_homologySphere, modulePiSphereGroupEquiv_naturality]
  have h := congrArg (fun ψ ↦ ψ.hom (modulePiMooreGroupEquiv W n s))
    (mooreHomologySphereIso_naturality f n)
  change (mooreHomologySphereIso V n).hom.hom
    ((HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
      (n + 1)).hom (modulePiMooreGroupEquiv W n s)) =
    sphereHomologyQuotientMap f n
      ((mooreHomologySphereIso W n).hom.hom (modulePiMooreGroupEquiv W n s)) at h
  rw [modulePiMooreGroupEquiv_homologySphere] at h
  exact h.symm
lemma modulePiMap_bijective_iff_homologyMap
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
      (moduleUnderlyingSSetMap_zero f)) ↔
    Function.Bijective
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
        (n + 1)).hom := by
  have h := funext (modulePiMooreGroupEquiv_naturality f n)
  exact ((modulePiMooreGroupEquiv V n).toEquiv.comp_bijective _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective h)).trans
      ((modulePiMooreGroupEquiv W n).toEquiv.bijective_comp _))
end SerrePositivity.InfinityCategories
