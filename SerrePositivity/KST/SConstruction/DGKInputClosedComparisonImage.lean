module
public import SerrePositivity.KST.SConstruction.DGKInputClosedComparison
public import SerrePositivity.KST.SConstruction.CoherentHomIntervalEdgeParameter
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso

/-! # 元の native 比較四角形の ν 像と同じ全 Hom 作用
概要：固定 S の標準比較四角形を、固定 ν の同じ native Hom 作用で厳密に照合する。
方針：標準 coherent 区間比較の豊穣自然性を使い、元の実 Perf 関手族を回収する。
規約：選択二単体の像を代用しない。使われ方：cone 比較の一回 Perf 延長像の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {P Q : PerfDGInput.{u, v} R}

/-- 任意の元の入力 Hom 族の標準四角形の ν 像は、同じ豊穣 Hom 作用の標準比較。 -/
lemma dgKInputNu_intervalFamily {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (SimplicialCategory.sHom P Q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison P Q) ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ (SSet.uliftFunctor).map
        ((presentedPerfectDGEnrichedExactFunctor R).map P Q) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (presentedPerfectDGStableQCat R P)
            (presentedPerfectDGStableQCat R Q)) := by
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGEnrichedExactFunctor R) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ P) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ Q)]
  congr 1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_enriched_naturality,
    ← Category.assoc]
  exact Category.assoc _ _ _

variable (f g : P ⟶ Q)
  (e : ForgetEnrichment.of (Complex R) f.down ≅ ForgetEnrichment.of (Complex R) g.down)
include e

/-- 元の指定 native Hom 辺を、標準 coherent 比較の入力区間として保持する。 -/
def dgKInputClosedIsoParameter : (Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (SimplicialCategory.sHom P Q) :=
  coherentHomIntervalEdgeParameter f g (dgKInputClosedIsoHomEdge R f g e)

/-- 元の標準比較四角形は、同じ指定入力区間の標準 coherent 区間比較そのもの。 -/
lemma dgKInputClosedIsoSquare_parameter :
    dgKInputClosedIsoSquare R f g e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (dgKInputClosedIsoParameter R f g e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison P Q) := by
  unfold dgKInputClosedIsoSquare
  congr 1
  exact coherentHomIntervalEdge_parameter f g (dgKInputClosedIsoHomEdge R f g e)

/-- 同じ元の native 比較区間を、固定 ν の同じ豊穣 Hom 作用へ送る。 -/
def dgKInputClosedIsoNuParameter :=
  dgKInputClosedIsoParameter R f g e ≫ (SSet.uliftFunctor).map
    ((presentedPerfectDGEnrichedExactFunctor R).map P Q)

/-- 元の比較四角形全体の ν 像は、元の入力区間の同じ豊穣作用による標準四角形。 -/
lemma dgKInputClosedIsoSquare_nu :
    dgKInputClosedIsoSquare R f g e ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgKInputClosedIsoNuParameter R f g e ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (presentedPerfectDGStableQCat R P)
          (presentedPerfectDGStableQCat R Q)) := by
  rw [dgKInputClosedIsoSquare_parameter]
  exact dgKInputNu_intervalFamily R (dgKInputClosedIsoParameter R f g e)

/-- 完全性と core の包含後に、同じ元の native Perf 関手族の全比較区間を回収する。 -/
lemma dgKInputClosedIsoNuParameter_ambient :
    dgKInputClosedIsoNuParameter R f g e ≫ (SSet.uliftFunctor).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (dgKInputStableValue R P) (dgKInputStableValue R Q) :
          SSet.{max (u + 1) v})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
            (dgKInputStableValue R P) (dgKInputStableValue R Q)).ι) =
      dgKInputClosedIsoParameter R f g e ≫ (SSet.uliftFunctor).map
        (presentedPerfectDGNativeFamilyMap R P Q) := by
  unfold dgKInputClosedIsoNuParameter
  rw [Category.assoc, ← Functor.map_comp]
  congr 1

end SerrePositivity.KST.SConstruction
