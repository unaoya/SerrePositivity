module
public import SerrePositivity.KST.SConstruction.CutIntervalExtensions
public import SerrePositivity.KST.SConstruction.CutSupportNormalization
public import SerrePositivity.KST.SConstruction.FullSubcomplexFunctorIsoReflection

/-! # 左右の支持部分圏と短い区間の S 構成の同値
概要：左右の支持部分圏を元の区間への制限と延長によって S_k C・S_(n-k) C と同値にする。
方針：短い区間上の合成は厳密な恒等、支持部分圏上の合成は正規化の関手同型を使う。
規約：対象類の対応だけでなく実際の quasicategory の逆データを構成する。
使われ方：相対切断の加法性から Segal 射への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Left 側の短い区間の延長の後の制限は完全関手として厳密に恒等。 -/
lemma cutLeftInterval_extension_restriction (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutLeftIntervalExtension n k X ≫ cutLeftIntervalRestriction n k X =
      𝟙 (sStableModel (k.val) X) := by
  apply Subtype.ext
  change (cutLeftIntervalExtensionMap n k X ≫
      (closedStableInclusion (cutLeftSupport n k X)).val) ≫
    sMap X.carrier (cutLeftIntervalInclusion n k) = _
  rw [cutLeftIntervalExtensionMap_inclusion, ← sMap_comp,
    cutLeftInterval_retraction_inclusion, sMap_id]
  rfl

/-- Left 側の支持部分圏上の制限と延長の合成は包含後に元の切断を回収する。 -/
lemma cutLeftInterval_restriction_extension_inclusion (n : ℕ) (k : Fin (n + 1))
    (X : StableModel.{u}) :
    (cutLeftIntervalRestriction n k X ≫ cutLeftIntervalExtension n k X).val ≫
        (closedStableInclusion (cutLeftSupport n k X)).val =
      (closedStableInclusion (cutLeftSupport n k X)).val ≫
        sMap X.carrier (cutCornerOrder k 0 0) := by
  change (((closedStableInclusion (cutLeftSupport n k X)).val ≫
    sMap X.carrier (cutLeftIntervalInclusion n k)) ≫ cutLeftIntervalExtensionMap n k X) ≫
      (closedStableInclusion (cutLeftSupport n k X)).val = _
  calc
    _ = (closedStableInclusion (cutLeftSupport n k X)).val ≫
        (sMap X.carrier (cutLeftIntervalInclusion n k) ≫
          (cutLeftIntervalExtensionMap n k X ≫
            (closedStableInclusion (cutLeftSupport n k X)).val)) := by
      simp only [Category.assoc]
    _ = (closedStableInclusion (cutLeftSupport n k X)).val ≫
        (sMap X.carrier (cutLeftIntervalInclusion n k) ≫
          sMap X.carrier (cutLeftIntervalRetraction n k)) :=
      congrArg (fun f => (closedStableInclusion (cutLeftSupport n k X)).val ≫
        (sMap X.carrier (cutLeftIntervalInclusion n k) ≫ f))
        (cutLeftIntervalExtensionMap_inclusion n k X)
    _ = _ := by rw [← sMap_comp, cutLeftInterval_inclusion_retraction]

/-- Left 側の支持部分圏上の制限と延長の合成は内部で恒等関手と同型。 -/
def cutLeftInterval_restriction_extensionIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cutLeftIntervalRestriction n k X ≫ cutLeftIntervalExtension n k X).val
      (𝟙 (closedSubcategory (cutLeftSupport n k X))) := by
  apply functorIsoOfFullSubcomplexPostcomp (cutLeftSupport n k X).predicate
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((cutLeftIntervalRestriction n k X ≫ cutLeftIntervalExtension n k X).val ≫
    (closedStableInclusion (cutLeftSupport n k X)).val)
    (𝟙 _ ≫ (closedStableInclusion (cutLeftSupport n k X)).val)
  rw [cutLeftInterval_restriction_extension_inclusion, Category.id_comp]
  exact (cutLeftSupport_normalizationIso n k X)

/-- Left 側の支持部分圏と短い区間の S 構成の実際の quasicategory 同値。 -/
def cutLeftIntervalEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (closedSubcategory (cutLeftSupport n k X))
      (sConstruction (k.val) X.carrier) where
  hom := (cutLeftIntervalRestriction n k X).val
  inv := (cutLeftIntervalExtension n k X).val
  homInvIso := cutLeftInterval_restriction_extensionIso n k X
  invHomIso := eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (congrArg Subtype.val (cutLeftInterval_extension_restriction n k X)))

/-- Right 側の短い区間の延長の後の制限は完全関手として厳密に恒等。 -/
lemma cutRightInterval_extension_restriction (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutRightIntervalExtension n k X ≫ cutRightIntervalRestriction n k X =
      𝟙 (sStableModel (n - k.val) X) := by
  apply Subtype.ext
  change (cutRightIntervalExtensionMap n k X ≫
      (closedStableInclusion (cutRightSupport n k X)).val) ≫
    sMap X.carrier (cutRightIntervalInclusion n k) = _
  rw [cutRightIntervalExtensionMap_inclusion, ← sMap_comp,
    cutRightInterval_retraction_inclusion, sMap_id]
  rfl

/-- Right 側の支持部分圏上の制限と延長の合成は包含後に元の切断を回収する。 -/
lemma cutRightInterval_restriction_extension_inclusion (n : ℕ) (k : Fin (n + 1))
    (X : StableModel.{u}) :
    (cutRightIntervalRestriction n k X ≫ cutRightIntervalExtension n k X).val ≫
        (closedStableInclusion (cutRightSupport n k X)).val =
      (closedStableInclusion (cutRightSupport n k X)).val ≫
        sMap X.carrier (cutCornerOrder k 1 1) := by
  change (((closedStableInclusion (cutRightSupport n k X)).val ≫
    sMap X.carrier (cutRightIntervalInclusion n k)) ≫ cutRightIntervalExtensionMap n k X) ≫
      (closedStableInclusion (cutRightSupport n k X)).val = _
  calc
    _ = (closedStableInclusion (cutRightSupport n k X)).val ≫
        (sMap X.carrier (cutRightIntervalInclusion n k) ≫
          (cutRightIntervalExtensionMap n k X ≫
            (closedStableInclusion (cutRightSupport n k X)).val)) := by
      simp only [Category.assoc]
    _ = (closedStableInclusion (cutRightSupport n k X)).val ≫
        (sMap X.carrier (cutRightIntervalInclusion n k) ≫
          sMap X.carrier (cutRightIntervalRetraction n k)) :=
      congrArg (fun f => (closedStableInclusion (cutRightSupport n k X)).val ≫
        (sMap X.carrier (cutRightIntervalInclusion n k) ≫ f))
        (cutRightIntervalExtensionMap_inclusion n k X)
    _ = _ := by rw [← sMap_comp, cutRightInterval_inclusion_retraction]

/-- Right 側の支持部分圏上の制限と延長の合成は内部で恒等関手と同型。 -/
def cutRightInterval_restriction_extensionIso (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cutRightIntervalRestriction n k X ≫ cutRightIntervalExtension n k X).val
      (𝟙 (closedSubcategory (cutRightSupport n k X))) := by
  apply functorIsoOfFullSubcomplexPostcomp (cutRightSupport n k X).predicate
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((cutRightIntervalRestriction n k X ≫ cutRightIntervalExtension n k X).val ≫
    (closedStableInclusion (cutRightSupport n k X)).val)
    (𝟙 _ ≫ (closedStableInclusion (cutRightSupport n k X)).val)
  rw [cutRightInterval_restriction_extension_inclusion, Category.id_comp]
  exact (cutRightSupport_normalizationIso n k X).symm

/-- Right 側の支持部分圏と短い区間の S 構成の実際の quasicategory 同値。 -/
def cutRightIntervalEquivalence (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (closedSubcategory (cutRightSupport n k X))
      (sConstruction (n - k.val) X.carrier) where
  hom := (cutRightIntervalRestriction n k X).val
  inv := (cutRightIntervalExtension n k X).val
  homInvIso := cutRightInterval_restriction_extensionIso n k X
  invHomIso := eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (congrArg Subtype.val (cutRightInterval_extension_restriction n k X)))

end SerrePositivity.KST.SConstruction
