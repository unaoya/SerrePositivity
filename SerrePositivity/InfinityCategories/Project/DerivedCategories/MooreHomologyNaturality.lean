module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MooreCyclesNaturality
/-!
概要：実 Moore ホモロジーと球面境界商の同型の自然性。
方針：元の実射を保ち、包含・cycles・ホモロジー射の可換式を照合する。
規約：正次数は n+1。使われ方：β5(g) の単体の弱同値と準同型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
def mooreShortHomologySphereIso (W : SimplicialObject (ModuleCat.{v} S)) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplex W n).homology ≅ ModuleCat.of S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereHomologyQuotient W n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplex W n).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreCyclesSphereEquiv W n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreCyclesSphereEquiv_range W n)).toModuleIso
lemma mooreShortHomologySphereIso_π (W : SimplicialObject (ModuleCat.{v} S)) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplex W n).homologyπ ≫ (mooreShortHomologySphereIso W n).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreAbstractCyclesSphereMap W n ≫
        ModuleCat.ofHom (LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n)).mkQ := by
  dsimp only [mooreShortHomologySphereIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreAbstractCyclesSphereMap, Iso.trans_hom]
  rw [← Category.assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  simp only [Category.assoc]
  congr 1
lemma mooreShortHomologySphereIso_naturality (f : W ⟶ V) (n : ℕ) :
    ShortComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplexMap f n) ≫
      (mooreShortHomologySphereIso V n).hom =
    (mooreShortHomologySphereIso W n).hom ≫ ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereHomologyQuotientMap f n) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplex W n).homologyπ).mp
  rw [← Category.assoc, ShortComplex.homologyπ_naturality]
  simp only [Category.assoc, mooreShortHomologySphereIso_π]
  conv_rhs => rw [← Category.assoc, mooreShortHomologySphereIso_π]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreAbstractCyclesSphereMap_naturality]
  simp only [Category.assoc]
  congr 1
lemma mooreHomologySphereIso_naturality (f : W ⟶ V) (n : ℕ) :
    HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
      (n + 1) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreHomologySphereIso V n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreHomologySphereIso W n).hom ≫ ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereHomologyQuotientMap f n) := by
  have ht := (HomologicalComplex.homologyFunctorIso' (ModuleCat.{v} S) (.down ℕ)
    (n + 2) (n + 1) n (by simp) (by simp)).hom.naturality
      ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
  change HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
      (n + 1) ≫
      (((normalizedMooreComplex (ModuleCat.{v} S)).obj V).homologyIsoSc'
        (n + 2) (n + 1) n (by simp) (by simp)).hom =
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homologyIsoSc'
        (n + 2) (n + 1) n (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleMooreShortComplexMap f n) at ht
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreHomologySphereIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc _
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj V).homologyIsoSc'
      (n + 2) (n + 1) n (by simp) (by simp)).hom, ht, Category.assoc]
  simpa only [mooreShortHomologySphereIso, Iso.trans_hom, Category.assoc] using!
    congrArg (fun ψ ↦
      (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homologyIsoSc'
        (n + 2) (n + 1) n (by simp) (by simp)).hom ≫ ψ)
      (mooreShortHomologySphereIso_naturality f n)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
