module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSuspensionAssemblyAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.PointedFamilyWhiskerNaturality
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionFunctor

/-! # 元の suspension 組み立ての同じ点つき値と全族
概要：元の点つき値・全入力族・組み立て成分を明示し、標準豊穣の自然性を保持する。
方針：元の basedHom 族の等号を、同じ全成分の前後合成の等号へ移す。
規約：元の豊穣関手の値・射を変更しない。使われ方：厳密自然変換への包装の分割。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の一次方向商の同じ suspension を標準点つき値として保持する。 -/
def presentedPerfectDGAssemblyObject (r : ℕ) (C : PerfDGInput.{u, v} A) :
    PointedSSetObject.{max (u + 1) v} :=
  ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (oneDirectionReducedRealization r
    (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)))⟩

/-- 元の一次方向の全族を同じ円で suspension した実写像族。 -/
def presentedPerfectDGAssemblyFamily (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (C ⟶[SSet.{max (u + 1) v}] D) ⟶
      (presentedPerfectDGAssemblyObject.{u, v} A r C ⟶[SSet]
        presentedPerfectDGAssemblyObject.{u, v} A r D) :=
  presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D ≫
    (Spectra.suspensionHom (presentedPerfectDGOneDirectionPointedObject.{u, v} A r C).obj
      (presentedPerfectDGOneDirectionPointedObject.{u, v} A r D).obj).right

/-- 同じ元の点つき値の間の、同じ suspension 組み立て成分。 -/
def presentedPerfectDGAssemblyObjectMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGAssemblyObject.{u, v} A r C ⟶
      presentedPerfectDGBoundaryPointedObject.{u, v} A (r + 1) C :=
  oneDirectionSuspensionAssembly r
    (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C))

/-- 元の全族の可換性を、同じ明示的な標準点つき値の上で回収する。 -/
lemma presentedPerfectDGAssemblyFamily_based (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGAssemblyFamily.{u, v} A r C D ≫
      pointedFamilyPost (presentedPerfectDGAssemblyObject.{u, v} A r C).obj
        (presentedPerfectDGAssemblyObject.{u, v} A r D).obj
        (presentedPerfectDGBoundaryPointedObject.{u, v} A (r + 1) D).obj
        (presentedPerfectDGAssemblyObjectMap.{u, v} A r D) =
    presentedPerfectDGBoundaryReducedFamilyMap.{u, v} A (r + 1) C D ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (presentedPerfectDGAssemblyObjectMap.{u, v} A r C)
        (presentedPerfectDGBoundaryPointedObject.{u, v} A (r + 1) D).obj := by
  ext n t
  exact types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGSuspensionAssembly_action.{u, v} A r C D) n) t

/-- 全族自然性は、同じ明示的な値の標準豊穣の前後合成にも厳密に可換。 -/
lemma presentedPerfectDGAssemblyFamily_whisker (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGAssemblyFamily.{u, v} A r C D ≫
      eHomWhiskerLeft SSet (presentedPerfectDGAssemblyObject.{u, v} A r C)
        (presentedPerfectDGAssemblyObjectMap.{u, v} A r D) =
    presentedPerfectDGBoundaryReducedFamilyMap.{u, v} A (r + 1) C D ≫
      eHomWhiskerRight SSet (presentedPerfectDGAssemblyObjectMap.{u, v} A r C)
        (presentedPerfectDGBoundaryPointedObject.{u, v} A (r + 1) D) :=
  pointedFamily_whisker_naturality _ _ _ _
    (presentedPerfectDGAssemblyObjectMap.{u, v} A r C)
    (presentedPerfectDGAssemblyObjectMap.{u, v} A r D) _ _
    (presentedPerfectDGAssemblyFamily_based.{u, v} A r C D)

end SerrePositivity.KST.SConstruction
