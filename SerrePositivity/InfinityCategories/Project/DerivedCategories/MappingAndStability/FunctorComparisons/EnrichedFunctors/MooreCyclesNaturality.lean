module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.ModuleSphereNaturality
/-!
概要：実 Moore cycles と球面単体の比較の自然性。
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
lemma normalizedMooreMap_arrow (f : W ⟶ V) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{v} S)).map f).f n ≫
      (NormalizedMooreComplex.objX V n).arrow =
    (NormalizedMooreComplex.objX W n).arrow ≫ f.app (op ⦋n⦌) := by
  simp only [normalizedMooreComplex_map, NormalizedMooreComplex.map_f,
    Subobject.factorThru_arrow]
abbrev moduleMooreShortComplex (W : SimplicialObject (ModuleCat.{v} S)) (n : ℕ) :=
  ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).sc' (n + 2) (n + 1) n
abbrev moduleMooreShortComplexMap (f : W ⟶ V) (n : ℕ) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} S) (.down ℕ)
    (n + 2) (n + 1) n).map ((normalizedMooreComplex (ModuleCat.{v} S)).map f)
def mooreAbstractCyclesSphereMap (W : SimplicialObject (ModuleCat.{v} S)) (n : ℕ) :
    (moduleMooreShortComplex W n).cycles ⟶ ModuleCat.of S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n) :=
  (moduleMooreShortComplex W n).moduleCatCyclesIso.hom ≫
    ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreCyclesSphereEquiv W n).toLinearMap
lemma mooreAbstractCyclesSphereMap_value (W : SimplicialObject (ModuleCat.{v} S)) (n : ℕ)
    (z : (moduleMooreShortComplex W n).cycles) :
    ((mooreAbstractCyclesSphereMap W n).hom z).val =
      (NormalizedMooreComplex.objX W (n + 1)).arrow.hom
        ((moduleMooreShortComplex W n).iCycles.hom z) := by
  have h := congrArg (fun ψ ↦ ψ.hom z)
    (moduleMooreShortComplex W n).moduleCatCyclesIso_hom_i
  exact congrArg (fun t ↦ (NormalizedMooreComplex.objX W (n + 1)).arrow.hom t) h
lemma mooreAbstractCyclesSphereMap_naturality (f : W ⟶ V) (n : ℕ) :
    ShortComplex.cyclesMap (moduleMooreShortComplexMap f n) ≫
      mooreAbstractCyclesSphereMap V n =
    mooreAbstractCyclesSphereMap W n ≫ ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModuleMap f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change ((mooreAbstractCyclesSphereMap V n).hom
    ((ShortComplex.cyclesMap (moduleMooreShortComplexMap f n)).hom z)).val = _
  rw [mooreAbstractCyclesSphereMap_value]
  have hc := congrArg (fun ψ ↦ ψ.hom z)
    (ShortComplex.cyclesMap_i (moduleMooreShortComplexMap f n))
  change (moduleMooreShortComplex V n).iCycles.hom
    ((ShortComplex.cyclesMap (moduleMooreShortComplexMap f n)).hom z) =
      (((normalizedMooreComplex (ModuleCat.{v} S)).map f).f (n + 1)).hom
        ((moduleMooreShortComplex W n).iCycles.hom z) at hc
  rw [hc]
  have ha := congrArg (fun ψ ↦ ψ.hom ((moduleMooreShortComplex W n).iCycles.hom z))
    (normalizedMooreMap_arrow f (n + 1))
  apply ha.trans
  change (f.app (op ⦋n + 1⦌)).hom
    ((NormalizedMooreComplex.objX W (n + 1)).arrow.hom
      ((moduleMooreShortComplex W n).iCycles.hom z)) =
    (f.app (op ⦋n + 1⦌)).hom ((mooreAbstractCyclesSphereMap W n).hom z).val
  rw [mooreAbstractCyclesSphereMap_value]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
