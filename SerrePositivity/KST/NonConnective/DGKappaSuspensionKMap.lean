module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKRoof
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFHomotopyFunctor
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
概要：同じ κ の選択 cone と平坦分解を保つ懸垂屋根の射作用。
方針：増大と可換な実 dg 射と perfect 保存を明示し、D 正本の商関手を使う。
規約：対象別の I・P の存在から入力射作用の存在を推論しない。
使われ方：反復懸垂の屋根の二脚を、固定 K 上でも同じ可換四角形として保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D E : Type v) [DGCategory R D] [DGCategory R E]
  [Small.{u} D] [Small.{u} E] {κ : Cardinal.{u}}
  (I : DGKappaConeInput R D κ) (J : DGKappaConeInput R E κ)

/-- 同じ二つの cone と、その指定平坦分解の増大を保つ射の明示データ。 -/
@[ext] structure DGKappaSuspensionMapData where
  cone : DGFunctor R (DGKappaCone R D I) (DGKappaCone R E J)
  resolved : DGFunctor R (DGCategoryCellResolution.Source R (DGKappaCone R D I))
    (DGCategoryCellResolution.Source R (DGKappaCone R E J))
  augmentation : resolved.comp (DGCategoryCellResolution.augmentation R (DGKappaCone R E J)) =
    (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).comp cone
  preservesPerfect : ∀ x ∈ dgKappaConePerfectObjects R D I,
    cone.obj x ∈ dgKappaConePerfectObjects R E J

/-- perfect を保つ同じ cone 射は、D 正本の元の比較関手で平坦分解の射へ持ち上がる。 -/
def DGKappaSuspensionMapData.ofConeFunctor
    (F : DGFunctor R (DGKappaCone R D I) (DGKappaCone R E J))
    (hF : ∀ x ∈ dgKappaConePerfectObjects R D I,
      F.obj x ∈ dgKappaConePerfectObjects R E J) : DGKappaSuspensionMapData R D E I J where
  cone := F
  resolved := DGCategoryCellResolution.comparisonFunctor R _ _ F
  augmentation := DGCategoryCellResolution.comparisonFunctor_augmentation R _ _ F
  preservesPerfect := hF

/-- 同じ選択 cone と同じ平坦分解の恒等射。 -/
def DGKappaSuspensionMapData.id : DGKappaSuspensionMapData R D D I I where
  cone := DGFunctor.id _
  resolved := DGFunctor.id _
  augmentation := by rw [strictDGFunctor_id_comp, strictDGFunctor_comp_id]
  preservesPerfect _ hx := hx

/-- 二つの同じ増大を保つ射は、元の dg 合成と perfect 保存で合成する。 -/
def DGKappaSuspensionMapData.comp
    {F : Type v} [DGCategory R F] [Small.{u} F] {K : DGKappaConeInput R F κ}
    (M : DGKappaSuspensionMapData R D E I J) (N : DGKappaSuspensionMapData R E F J K) :
    DGKappaSuspensionMapData R D F I K where
  cone := M.cone.comp N.cone
  resolved := M.resolved.comp N.resolved
  augmentation := by
    rw [strictDGFunctor_comp_assoc, N.augmentation, ← strictDGFunctor_comp_assoc,
      M.augmentation, strictDGFunctor_comp_assoc]
  preservesPerfect x hx := N.preservesPerfect _ (M.preservesPerfect x hx)

variable (M : DGKappaSuspensionMapData R D E I J)

/-- 同じ平坦分解の射は、懸垂で零化する同じ対象集合を保つ。 -/
theorem dgKappaSuspensionMap_preservesNullObjects :
    ∀ x ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I),
      M.resolved.obj x ∈
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J) := by
  intro x hx
  have h := congrArg (fun F => F.obj x) M.augmentation
  change (DGCategoryCellResolution.augmentation R (DGKappaCone R E J)).obj
    (M.resolved.obj x) =
      M.cone.obj ((DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x) at h
  change (DGCategoryCellResolution.augmentation R (DGKappaCone R E J)).obj
    (M.resolved.obj x) ∈ dgKappaConePerfectObjects R E J
  rw [h]
  exact M.preservesPerfect _ hx

/-- D 正本の商関手を同じ零化対象へ適用した、元の懸垂間の厳密 dg 入力射。 -/
def dgKappaSuspensionInputMap : dgKappaSuspensionKInput R D I ⟶ dgKappaSuspensionKInput R E J :=
  ULift.up (DGQuotient.quotientDGFunctor R
    (DGCategoryCellResolution.Source R (DGKappaCone R D I))
    (DGCategoryCellResolution.Source R (DGKappaCone R E J)) M.resolved
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J))
    (dgKappaSuspensionMap_preservesNullObjects R D E I J M))

/-- 同じ懸垂屋根の右脚は、固定 dg 入力の通常射として厳密に自然。 -/
theorem dgKappaSuspensionInputMap_projection :
    dgKappaResolvedSuspensionInputMap R D I ≫ dgKappaSuspensionInputMap R D E I J M =
      (ULift.up M.resolved : dgKappaResolvedConeKInput R D I ⟶ dgKappaResolvedConeKInput R E J) ≫
        dgKappaResolvedSuspensionInputMap R E J := by
  apply ULift.ext
  exact DGQuotient.quotientDGFunctor_inclusion R _ _ _ _ _ _

/-- 元の増大の固定 K 像は、同じ厳密な屋根の射に沿って可換する。 -/
theorem dgKappaSuspensionKMap_augmentation :
    CommSq (dgKInputSpectrumMap R (dgKappaResolvedConeAugmentationInputMap R D I))
      (dgKInputSpectrumMap R
        (ULift.up M.resolved : dgKappaResolvedConeKInput R D I ⟶ dgKappaResolvedConeKInput R E J))
      (dgKInputSpectrumMap R (ULift.up M.cone : dgKappaConeKInput R D I ⟶ dgKappaConeKInput R E J))
      (dgKInputSpectrumMap R (dgKappaResolvedConeAugmentationInputMap R E J)) := by
  constructor
  rw [← presentedPerfectDGBFMap_comp, ← presentedPerfectDGBFMap_comp]
  congr 1
  apply ULift.ext
  exact M.augmentation.symm

/-- 元の商包含の固定 K 像も、同じ厳密な懸垂入力射に沿って可換する。 -/
theorem dgKappaSuspensionKMap_projection :
    CommSq (dgKInputSpectrumMap R (dgKappaResolvedSuspensionInputMap R D I))
      (dgKInputSpectrumMap R
        (ULift.up M.resolved : dgKappaResolvedConeKInput R D I ⟶ dgKappaResolvedConeKInput R E J))
      (dgKInputSpectrumMap R (dgKappaSuspensionInputMap R D E I J M))
      (dgKInputSpectrumMap R (dgKappaResolvedSuspensionInputMap R E J)) := by
  constructor
  rw [← presentedPerfectDGBFMap_comp, ← presentedPerfectDGBFMap_comp,
    dgKappaSuspensionInputMap_projection]

end SerrePositivity.KST.NonConnective
