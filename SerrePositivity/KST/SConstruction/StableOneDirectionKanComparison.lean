module
public import SerrePositivity.KST.SConstruction.StableOneDirectionPointedComparison
public import SerrePositivity.KST.Fibration.DGNuSBoundaryInfinity
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization

/-!
概要：元の S₁ 商比較を同じ Ex∞ に移し、全図式の点つき同型を得る。
方針：全族自然変換を後合成し、元の比較の弱同値性を各成分で使う。
規約：逆の厳密自然性を仮定しない。使われ方：有限 native BF 隣接段 span の左脚。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open Fibration SimplicialModel

/-- 概要：同じ一次方向商と全自然同値族の Ex∞ 値。
方針：元の点つき段関手を同じ Kan 置換へ後合成する。
規約：全 Hom を保持。使われ方：隣接段の元の左脚の始域。 -/
def stableOneDirectionKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedKanObject.{u} :=
  (stableOneDirectionPointedEnrichedFunctor r).comp SSet exInfinityPointedKanEnrichedFunctor

/-- 概要：同じ元の S₁ 比較の Ex∞ 像。
方針：同じ点つき比較を Kan 値間の射へ送る。
規約：元の実比較を保持。使われ方：全族変換の成分。 -/
def stableOneDirectionKanComparisonMap (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionKanEnrichedFunctor r).obj C ⟶
      (stableSBoundaryKanEnrichedFunctor r).obj C :=
  exInfinityPointedKanMap (stableOneDirectionPointedComparisonMap r C)

/-- 概要：全自然同値族に厳密に自然な、元の Kan S₁ 比較。
方針：同じ点つき変換を Ex∞ へ後合成する。
規約：全高次入力を保持。使われ方：同じ二胞体の比較。 -/
def stableOneDirectionKanComparison (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableOneDirectionKanEnrichedFunctor r) (stableSBoundaryKanEnrichedFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _ exInfinityPointedKanEnrichedFunctor
    (stableOneDirectionPointedComparison r)

/-- 概要：変換成分は同じ元の比較の Ex∞ 像。
方針：厳密豊穣後合成の成分を回収する。
規約：元の射を固定する。使われ方：可逆性の成分判定。 -/
lemma stableOneDirectionKanComparison_app (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionKanComparison r).app C =
      eHomEquiv SSet (stableOneDirectionKanComparisonMap r C) :=
  exInfinityPointedKanEnrichedFunctor_hom (stableOneDirectionPointedComparisonMap r C)

/-- 概要：同じ Kan S₁ 比較は全基点・全次数で π 同型。
方針：元の比較の局所化可逆性を同じ Ex∞ に移す。
規約：追加の完備性入力なし。使われ方：元の比較辺の可逆性。 -/
lemma stableOneDirectionKanComparisonMap_piIsomorphism (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (stableOneDirectionKanComparisonMap r C).hom.right := by
  apply kanPiIsomorphism_of_localized_isIso
  change IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
    (oneDirectionReducedComparison r (stableCategoryModel C)).right))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
    (oneDirectionReducedComparison_localized_isIso r (stableCategoryModel C))

/-- 概要：同じ S₁ 比較は全図式を保つ点つき Kan 関手同型。
方針：元の全族変換と各成分の点つき Whitehead を使う。
規約：BF 関手を構成しない。使われ方：有限 native 全四角形の隣接段比較。 -/
def stableOneDirectionKanComparisonFunctorIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableOneDirectionKanEnrichedFunctor.{u} r))
      (stableSBoundaryKanInfinityFunctor r) :=
  Spectra.StrictEnrichedTransformation.functorIso _ _ (stableOneDirectionKanComparison r) (by
    intro C
    have h := strictSimplicialTransformation_componentHom _ _ _ C _
      (stableOneDirectionKanComparison_app r C)
    rw [h]
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
      (stableOneDirectionKanComparisonMap_piIsomorphism r C))

end SerrePositivity.KST.SConstruction
