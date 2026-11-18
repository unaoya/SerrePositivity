module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainContraction
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit

/-!
概要：複体の指定単体収縮の順射を元の AW 余単位と照合する。
方針：single₀ への鎖写像を零次の全頂点で比較する。
規約：HA 1.3.1.13、Berger–Fresse §1.1.4、同じ augmentation。
使われ方：M10 の加群の全評価と複体側の指定三角形の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.SimplicialChains.AlexanderWhitney
variable (A : Type u) [CommRing A]

/-- 概要：指定鎖収縮の順射は元の AW augmentation。
方針：single₀ の普遍性と全頂点での式を使う。
規約：HA 1.3.1.13、元の射。使われ方：コチェインの全評価。 -/
lemma normalizedSimplexChainContraction_hom_counit (n : SimplexCategory) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj n) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom.f 0 =
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A (SSet.stdSimplex.obj n)
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A (SSet.stdSimplex.obj n) 0
  intro x
  refine Eq.trans ?_ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator A (SSet.stdSimplex.obj n) x).symm
  simp only [_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction, HomotopyEquiv.trans_hom,
    HomotopyEquiv.ofIso, HomologicalComplex.comp_f,
    AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex_hom,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
    ChainComplex.single₀_map_f_zero, Functor.mapIso_hom, Iso.trans_hom,
    ModuleCat.comp_apply]
  have hp := congrArg (fun f => f.f 0)
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
      ((BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n)))
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A (SSet.stdSimplex.obj n)).f 0 ≫
    (AlgebraicTopology.inclusionOfMooreComplexMap
      ((BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).f 0 = _ at hp
  rw [AlgebraicTopology.DoldKan.PInfty_f_0] at hp
  have hg := ConcreteCategory.congr_hom hp (ModuleCat.freeMk (ULift.up x))
  change (AlgebraicTopology.inclusionOfMooreComplexMap
    ((BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).f 0
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (SSet.stdSimplex.obj n) 0 x) = ModuleCat.freeMk (ULift.up x) at hg
  rw [hg]
  change (BarrattEccles.singletonFreeIso A).hom
    ((ModuleCat.free A).map _ ((ModuleCat.free A).map _ (ModuleCat.freeMk (ULift.up x)))) = _
  simp only [ModuleCat.free_map_apply]
  simp only [BarrattEccles.singletonFreeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ModuleCat.comp_apply, ModuleCat.free_map_apply,
    ModuleCat.FreeMonoidal.εIso_inv_freeMk]
  exact ModuleCat.FreeMonoidal.εIso_inv_freeMk A _

/-- 概要：指定コチェイン収縮の順射は同じ AW 余単位。
方針：元の鎖写像の等式を同じ次数延長に沿って送る。
規約：HA 1.3.1.13、整数次数の実射。使われ方：同じ frame augmentation の比較。 -/
lemma normalizedSimplexCochainContraction_hom_counit (n : SimplexCategory) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) := by
  change HomologicalComplex.extendMap (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom
    ComplexShape.embeddingDownNat ≫ _ = _
  rw [normalizedSimplexChainContraction_hom_counit]
  rfl

end SerrePositivity.EInfinity.Modules
