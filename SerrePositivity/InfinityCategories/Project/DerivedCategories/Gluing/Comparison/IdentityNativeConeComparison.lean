module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityConeComparisonCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityRightAxisPerfectConeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityRightAxisLaxDifference
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.IdentityConeDiagonalZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.NativePerfectYonedaEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.PerfectValuedFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Pretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
/-!
概要：恒等 Hom gluing の元実 cone 関手を、同じ native lax 比較後の選択 cofiber 差へ全比較する。
方針：実右軸の全同型・対角の指定収縮・小 Perf 像による完全性を局所化判定へ代入する。
規約：元の cone 関手と元の全比較を保持し、全 Perf の Small 性を要求しない。
使われ方：固定入力の恒等 cone 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C]
local notation "I" => _root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C M
attribute [local irreducible] dgHomGluingBimodule
local instance dgGluingIdentityNativeBase_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R C
local instance dgGluingIdentityNativeSource_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C C M inferInstance inferInstance
local instance dgGluingIdentityNativeSource_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R G) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNerve_isStable R C C M inferInstance inferInstance
local instance dgGluingIdentityNativePerfect_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R C)) := (perfectDGStableModel R C Set.univ).stable

def dgGluingIdentityNativeConeComparison (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C))
    (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePerfectYonedaEquivalence R C hC).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomGluingConeFunctor R C C C I I)) := by
  let B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C, inferInstance, inferInstance⟩
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
  let y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePerfectYonedaEquivalence R C hC
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomGluingConeFunctor R C C C I I)
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C)
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgGluingRightAxis R C C M z hz)
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgPerfectValuedFunctor_isExactFunctor R G C
    (dgHomGluingConeFunctor R C C C I I)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ e.hom) (_root_.SerrePositivity.KST.LocalizingInvariants.IdentityLax.exactDiagonal B).hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonalIso.{u, 0} R C
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((j ≫ e.hom) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.exactLaxDifference (𝟙 B) (𝟙 B)).hom) (𝟙 B.obj) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityRightAxisLaxDifferenceIso R C z hz
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso y.hom (j ≫ f) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityRightAxisPerfectConeIso R C z hz) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _)
  have hz' : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((i ≫ f).app (Opposite.op ⦋0⦌) x) := by
    intro x
    obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C).symm.surjective x
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomGluingConeFunctor R C C C I I)).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R C) x,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (dgHomGluingConeFunctor R C C C I I)]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityConeDiagonal_vertex_zero R C x
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityConeComparisonCriterion B e y f i j hi hj hf hz'

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
