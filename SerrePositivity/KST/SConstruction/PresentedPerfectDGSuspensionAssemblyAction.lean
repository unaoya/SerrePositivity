module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyQuotientAction
public import SerrePositivity.KST.SConstruction.CofiberSuspensionFamilyNaturality
public import SerrePositivity.KST.SConstruction.SuspensionAssemblyEvaluation

/-! # 元の suspension 組み立てと全 native dg 入力族
概要：一次方向の同じ境界商の suspension 組み立ては、全 native 関手族と可換する。
方針：元の区間組み立ての可換性と商射回収を、全写像族の降下定理へ渡す。
規約：通常射や頂点の等式に弱めない。使われ方：BF K の隣接段の構造写像比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories Spectra
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の suspension 組み立ては、全 native Kan dg 入力族について厳密に自然である。 -/
lemma presentedPerfectDGSuspensionAssembly_action (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
      (suspensionHom
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)))).right ≫
      (PointedObject.basedHomMap
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))))
        (oneDirectionSuspensionAssembly r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)))).right =
    presentedPerfectDGBoundaryReducedFamilyMap A (r + 1) C D ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (oneDirectionSuspensionAssembly r
        (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (boundaryReducedRealization (r + 1)
          (stableCategoryModel (presentedPerfectDGStableCategory A D))) := by
  let X := stableCategoryModel (presentedPerfectDGStableCategory A C)
  let Y := stableCategoryModel (presentedPerfectDGStableCategory A D)
  let U := oneDirectionReducedRealization r X
  let V := oneDirectionReducedRealization r Y
  let W := boundaryReducedRealization (r + 1) Y
  let σ := oneDirectionSuspensionAssembly r X
  let σ' := oneDirectionSuspensionAssembly r Y
  let a := presentedPerfectDGOneDirectionReducedFamilyMap A r C D
  let b := presentedPerfectDGBoundaryReducedFamilyMap A (r + 1) C D
  let s := presentedPerfectDGOneDirectionAction A (r + 1) C D
  change a ≫ (suspensionHom U V).right ≫
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U) σ').right = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre σ W
  apply cofiberTensorFamily_hom_ext
    (P := C ⟶[SSet.{max (u + 1) v}] D) (boundary.{max (u + 1) v} 1).ι
    (oneDirectionFatBoundary (r + 1) X).ι W
  rw [← Category.assoc a (suspensionHom U V).right
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U) σ').right]
  erw [Category.assoc, pointedFamily_post_evaluation (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U)
    (a ≫ (suspensionHom U V).right) σ', pointedFamily_pre_evaluation σ W b]
  ext n z
  have he := suspensionHom_family_app U V a n
    ((PointedObject.cofiberQuotient (boundary.{max (u + 1) v} 1).ι).app n z.1.1)
    ((oneDirectionReductionQuotient r X).app n z.1.2) z.2
  have hs := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedFamilyMap_quotient A r C D) n) (z.1.2, z.2)
  have hl := types_congr_hom (NatTrans.congr_app
    (oneDirectionSuspensionAssembly_underlying r X) n) z.1
  have hr := types_congr_hom (NatTrans.congr_app
    (oneDirectionSuspensionAssembly_underlying r Y) n) (z.1.1, s.app n (z.1.2, z.2))
  have hn := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGAssemblyQuotient_action A r C D) n) z
  exact (congrArg (fun x => σ'.right.app n x) he).trans
    ((congrArg (fun x => σ'.right.app n ((PointedSimplicialSet.productToSmash
      PointedSimplicialSet.circle V).app n
        ((PointedObject.cofiberQuotient (boundary.{max (u + 1) v} 1).ι).app n z.1.1, x)))
        hs).trans (hr.trans (hn.symm.trans
          (congrArg (fun x => (uncurry (b ≫ PointedObject.basedHomι
            (boundaryReducedRealization (r + 1) X) W)).app n (x, z.2)) hl.symm))))

end SerrePositivity.KST.SConstruction
