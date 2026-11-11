module
public import SerrePositivity.KST.SConstruction.StableKanAssemblySpan
public import SerrePositivity.KST.SConstruction.StableOneDirectionKanComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformationWhisker
public import SerrePositivity.KST.SConstruction.SuspensionLocalizedEquivalence

/-!
概要：元の隣接段 span の実両脚と全 Hom 自然性・左脚の弱同値性を回収する。
方針：同じ二変換の実成分を回収し、元の Kan S₁ 比較を suspension する。
規約：比較の逆は選ばない。使われ方：有限 native BF 再帰の実 span 入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open Spectra SimplicialModel

/-- 概要：元の左変換の成分は同じ Kan S₁ 比較の suspension。
方針：同じ全 Hom 後合成の実射回収式を使う。
規約：元の比較を保持。使われ方：全 Hom 左自然性の成分。 -/
lemma stableKanAssemblyLeftTransformation_app (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblyLeftTransformation r).app C =
      eHomEquiv SSet (stableKanAssemblyLeftMap r C) :=
  exInfinityThenSuspensionFunctor_hom (stableOneDirectionPointedComparisonMap r C)

/-- 概要：元の右変換は同じ比較と組み立て像の実合成を回収する。
方針：同じ二変換の成分回収式を合成する。
規約：元の実射を保持。使われ方：全 Hom 右自然性の成分。 -/
lemma stableKanAssemblyRightTransformation_app (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblyRightTransformation r).app C =
      eHomEquiv SSet (stableKanAssemblyRightMap r C) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp_hom _ _ _ _ _ C _ _
    (exInfinitySuspensionTransformation_app ((stableOneDirectionPointedEnrichedFunctor r).obj C))
    (coaugmentedPointedEnrichedFunctor_hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
      (stableSuspensionAssemblyMap r C))

/-- 概要：同じ実左脚は全高次 Hom の前後合成に自然。
方針：元の全族変換の実成分を回収する。
規約：入力を離散化しない。使われ方：有限 BF 次段の左可換式。 -/
lemma stableKanAssemblyLeft_whisker (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblySourceFunctor r).map C D ≫
        eHomWhiskerLeft SSet ((stableKanAssemblySourceFunctor r).obj C)
          (stableKanAssemblyLeftMap r D) =
      (stableKanAssemblyLeftTargetFunctor r).map C D ≫
        eHomWhiskerRight SSet (stableKanAssemblyLeftMap r C)
          ((stableKanAssemblyLeftTargetFunctor r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _ (stableKanAssemblyLeftTransformation r)
    (stableKanAssemblyLeftMap r) (stableKanAssemblyLeftTransformation_app r) C D

/-- 概要：同じ実右脚も全高次 Hom の前後合成に自然。
方針：元の合成全族変換の実成分を回収する。
規約：全二胞体を保持。使われ方：有限 BF 次段の右可換式。 -/
lemma stableKanAssemblyRight_whisker (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblySourceFunctor r).map C D ≫
        eHomWhiskerLeft SSet ((stableKanAssemblySourceFunctor r).obj C)
          (stableKanAssemblyRightMap r D) =
      (stableKanAssemblyTargetFunctor r).map C D ≫
        eHomWhiskerRight SSet (stableKanAssemblyRightMap r C)
          ((stableKanAssemblyTargetFunctor r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _ (stableKanAssemblyRightTransformation r)
    (stableKanAssemblyRightMap r) (stableKanAssemblyRightTransformation_app r) C D

/-- 概要：同じ元の左脚は anodyne 局所化で可逆。
方針：同じ Kan S₁ 比較の π 同型を suspension へ送る。
規約：追加の比較入力なし。使われ方：有限 BF 次段比較の弱同値性。 -/
lemma stableKanAssemblyLeftMap_localized_isIso (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((stableKanAssemblySourceFunctor r).obj C).obj ⟶
        ((stableKanAssemblyLeftTargetFunctor r).obj C).obj from
          stableKanAssemblyLeftMap r C).right) :=
  suspensionImage_isIso_of_piIsomorphism AnodyneHomotopy.anodyneQ
    (Localization.inverts _ anodyneExtensions) (stableOneDirectionKanComparisonMap r C).hom
    (stableOneDirectionKanComparisonMap_piIsomorphism r C)

end SerrePositivity.KST.SConstruction
