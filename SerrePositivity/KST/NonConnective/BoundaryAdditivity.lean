module

public import SerrePositivity.KST.SConstruction.MultiRealizationAdditivity
public import SerrePositivity.KST.SConstruction.BoundaryRealizationInvariance
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-!
概要：既存 S• 加法性を、同じ全零境界商の点つき Kan 射対へ移す。
方針：元の実現から商・Kan 置換への自然な比較を使い、直積と比較射を打ち消す。
規約：加法性を入力仮定に加えず、正反復の既存定理から証明する。
使われ方：同じ BF K の swindle の群への作用の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 正反復の元の実現から同じ境界商 Kan 模型への実比較。 -/
def boundaryKanQuotient (r : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor (r + 1)).obj X ⟶
      ((boundaryKanRealizationFunctor r).obj X).right :=
  boundaryReductionQuotient r X ≫
    (PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right

/-- 同じ比較は元の完全射に関して厳密に自然。 -/
lemma boundaryKanQuotient_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanQuotient r X ≫ ((boundaryKanRealizationFunctor r).map f).right =
      (multiRealizationFunctor (r + 1)).map f ≫ boundaryKanQuotient r Y := by
  unfold boundaryKanQuotient
  have h := congrArg Under.Hom.right
    (PointedKanReplacement.unit.naturality (boundaryReducedRealizationMap r f)).symm
  change (PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right ≫
    ((boundaryKanRealizationFunctor r).map f).right =
      (boundaryReducedRealizationMap r f).right ≫
        (PointedKanReplacement.unit.app (boundaryReducedRealization r Y)).right at h
  rw [Category.assoc, h, ← Category.assoc, boundaryReducedRealizationMap_quotient,
    Category.assoc]

/-- 元の商と anodyne 単位の合成は局所化で可逆。 -/
lemma boundaryKanQuotient_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (boundaryKanQuotient r X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have := (Localization.inverts Q anodyneExtensions) _
    (PointedKanReplacement.unit_anodyne (boundaryReducedRealization r X))
  change IsIso (Q.map (_ ≫ _))
  rw [Q.map_comp]
  infer_instance

/-- 同じ境界商 Kan 模型の subobject・quotient の実点つき射対。 -/
def boundaryKanAdditivityMap (r : ℕ) (X : StableModel.{u}) :
    (boundaryKanRealizationFunctor r).obj (cofiberStableModel X) ⟶
      PointedObject.prod ((boundaryKanRealizationFunctor r).obj X)
        ((boundaryKanRealizationFunctor r).obj X) :=
  PointedObject.prodLift
    ((boundaryKanRealizationFunctor r).map (cofiberStableSubobject X))
    ((boundaryKanRealizationFunctor r).map (cofiberStableQuotient X))

/-- 元の正反復加法性と同じ点つき射対は実比較に関して可換。 -/
lemma boundaryKanAdditivityMap_comparison (r : ℕ) (X : StableModel.{u}) :
    boundaryKanQuotient r (cofiberStableModel X) ≫ (boundaryKanAdditivityMap r X).right =
      multiRealizationAdditivityMap (r + 1) X ≫
        (boundaryKanQuotient r X ⊗ₘ boundaryKanQuotient r X) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [boundaryKanAdditivityMap, PointedObject.prodLift, Category.assoc,
      tensorHom_fst, multiRealizationAdditivityMap, lift_fst_assoc]
    exact boundaryKanQuotient_naturality r (cofiberStableSubobject X)
  · simp only [boundaryKanAdditivityMap, PointedObject.prodLift, Category.assoc,
      tensorHom_snd, multiRealizationAdditivityMap, lift_snd_assoc]
    exact boundaryKanQuotient_naturality r (cofiberStableQuotient X)

/-- 境界商 Kan 射対の加法性は、既存の正反復 S• 加法性から従う。 -/
theorem boundaryKanAdditivityMap_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (boundaryKanAdditivityMap r X).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  let q := boundaryKanQuotient r X
  have hq := boundaryKanQuotient_localized_isIso r X
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso q hq
    ((multiRealizationFunctor (r + 1)).obj X)
  have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso q hq
    (((boundaryKanRealizationFunctor r).obj X).right)
  have hprod : IsIso (Q.map (q ⊗ₘ q)) := by
    rw [tensorHom_def, Q.map_comp]
    infer_instance
  have := multiRealizationAdditivityMap_localized_isIso r X
  have := boundaryKanQuotient_localized_isIso r (cofiberStableModel X)
  have h := congrArg Q.map (boundaryKanAdditivityMap_comparison r X)
  rw [Q.map_comp, Q.map_comp] at h
  have hc : IsIso (Q.map (boundaryKanQuotient r (cofiberStableModel X)) ≫
      Q.map (boundaryKanAdditivityMap r X).right) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

/-- 同じ点つき射対は、全基点・全自然数次数で π_* 同型。 -/
theorem boundaryKanAdditivityMap_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryKanAdditivityMap r X).right :=
  kanPiIsomorphism_of_localized_isIso _ (boundaryKanAdditivityMap_localized_isIso r X)

end SerrePositivity.KST.NonConnective
