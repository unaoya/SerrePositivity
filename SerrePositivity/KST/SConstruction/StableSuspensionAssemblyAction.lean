module
public import SerrePositivity.KST.SConstruction.StableOneDirectionReducedAction
public import SerrePositivity.KST.SConstruction.StableBoundaryReducedAction
public import SerrePositivity.KST.SConstruction.ParameterizedQuotientSquare
public import SerrePositivity.KST.SConstruction.CofiberSuspensionFamilyNaturality
public import SerrePositivity.KST.SConstruction.SuspensionAssemblyEvaluation

/-!
概要：元の suspension 組み立ての全自然同値族に対する自然性。
方針：同じ全 core 図式の区間作用と、二つの元の商射の回収式を使う。
規約：元の組み立てと二胞体を保つ。使われ方：有限 native BF 再帰の右脚。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open InfinityCategories LocalizingInvariants Spectra
open scoped Simplicial

/-- 概要：同じ商射の像で元の全基点固定族を回収する。
方針：同じ basedHom 包含の評価式と元の商射回収式を合成する。
規約：全パラメータの等式。使われ方：組み立て自然性の商条件。 -/
lemma stableOneDirectionReducedFamilyMap_quotient (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (oneDirectionReductionQuotient r (stableCategoryModel C) ▷ (C ⟶[SSet.{u}] D)) ≫
        uncurry (stableOneDirectionReducedFamilyMap r C D ≫ PointedObject.basedHomι
          (oneDirectionReducedRealization r (stableCategoryModel C))
          (oneDirectionReducedRealization r (stableCategoryModel D))) =
      stableOneDirectionAction (r + 1) C D ≫
        oneDirectionReductionQuotient r (stableCategoryModel D) := by
  have he := (congrArg (uncurry (C := SSet.{u}))
    (stableOneDirectionReducedFamilyMap_inclusion r C D)).trans (uncurry_curry _)
  exact (congrArg
    ((oneDirectionReductionQuotient r (stableCategoryModel C) ▷ (C ⟶[SSet.{u}] D)) ≫ ·)
      he).trans (stableOneDirectionReducedAction_quotient r C D)

/-- 概要：元の区間組み立ては全自然同値入力族に厳密に自然。
方針：全 core 図式の対角組み立ての自然性を同じ添字に適用する。
規約：全単体を保持する。使われ方：同じ標的商への自然性。 -/
lemma stableMultiDiagonalAssembly_action (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (multiDiagonalAssembly r (stableCategoryModel C) ▷ (C ⟶[SSet.{u}] D)) ≫
        stableMultiRealizationAction (r + 1) C D =
      (α_ (Δ[1] : SSet.{u})
        ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C))
        (C ⟶[SSet.{u}] D)).hom ≫
          ((Δ[1] : SSet.{u}) ◁ stableOneDirectionAction r C D) ≫
            multiDiagonalAssembly r (stableCategoryModel D) :=
  coordinateDiagonalAssembly_enriched_naturality r (stableMultiSCoreEnrichedDiagram (r + 1)) C D

/-- 概要：同じ元の標的商を取った区間組み立ても全族に自然。
方針：元の区間自然性と同じ商射の全族可換式を合成する。
規約：元の商射を保つ。使われ方：suspension への自然性の降下。 -/
lemma stableAssemblyQuotient_action (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((multiDiagonalAssembly (r + 1) (stableCategoryModel C) ≫
        boundaryReductionQuotient (r + 1) (stableCategoryModel C)) ▷
          (C ⟶[SSet.{u}] D)) ≫ stableBoundaryReducedAction (r + 1) C D =
      (α_ (Δ[1] : SSet.{u})
        ((oneDirectionRealizationFunctor (r + 1)).obj (stableCategoryModel C))
        (C ⟶[SSet.{u}] D)).hom ≫
          ((Δ[1] : SSet.{u}) ◁ stableOneDirectionAction (r + 1) C D) ≫
            multiDiagonalAssembly (r + 1) (stableCategoryModel D) ≫
              boundaryReductionQuotient (r + 1) (stableCategoryModel D) :=
  parameterizedQuotientSquare _ _ _ _ _ _ _
    (stableMultiDiagonalAssembly_action (r + 1) C D)
    (stableBoundaryReducedAction_quotient (r + 1) C D)

/-- 概要：同じ元の suspension 組み立ては全基点固定族と可換。
方針：元の二商射を回収する一般の降下定理へ同じ実区間自然性を渡す。
規約：元の全高次入力を保つ。使われ方：有限 BF 隣接段 span の右脚の厳密自然性。 -/
lemma stableSuspensionAssembly_action (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableOneDirectionReducedFamilyMap r C D ≫
      (suspensionHom (oneDirectionReducedRealization r (stableCategoryModel C))
        (oneDirectionReducedRealization r (stableCategoryModel D))).right ≫
      (PointedObject.basedHomMap
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (oneDirectionReducedRealization r (stableCategoryModel C)))
        (oneDirectionSuspensionAssembly r (stableCategoryModel D))).right =
      stableBoundaryReducedFamilyMap (r + 1) C D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
        (oneDirectionSuspensionAssembly r (stableCategoryModel C))
        (boundaryReducedRealization (r + 1) (stableCategoryModel D)) := by
  have he := (congrArg (uncurry (C := SSet.{u}))
    (stableBoundaryReducedFamilyMap_inclusion (r + 1) C D)).trans (uncurry_curry _)
  have hn := (congrArg
    (((multiDiagonalAssembly (r + 1) (stableCategoryModel C) ≫
      boundaryReductionQuotient (r + 1) (stableCategoryModel C)) ▷ (C ⟶[SSet.{u}] D)) ≫ ·)
    he).trans (stableAssemblyQuotient_action r C D)
  exact cofiberSuspensionFamily_naturality
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel D)).ι _ _
    (oneDirectionSuspensionAssembly r (stableCategoryModel C))
    (oneDirectionSuspensionAssembly r (stableCategoryModel D))
    (stableOneDirectionReducedFamilyMap r C D) (stableBoundaryReducedFamilyMap (r + 1) C D)
    (stableOneDirectionAction (r + 1) C D) _ _
    (stableOneDirectionReducedFamilyMap_quotient r C D)
    (oneDirectionSuspensionAssembly_underlying r (stableCategoryModel C))
    (oneDirectionSuspensionAssembly_underlying r (stableCategoryModel D)) hn

end SerrePositivity.KST.SConstruction
