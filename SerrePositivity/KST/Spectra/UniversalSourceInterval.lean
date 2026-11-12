module

public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus
public import SerrePositivity.KST.Spectra.PointedRlpSection
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace

/-!
概要：指定した源の一つの普遍区間を、全標的の全写像族へ同じ anodyne 制限から移す。
方針：基点固定切断で族を延長し、同じ源区間による前合成を制限する。
規約：標的ごとの成分等式から区間を選ばない。使われ方：交換符号区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra

/-- 実際の anodyne な単位とその上の一つの実区間を持つ、普遍入力のデータ。 -/
structure UniversalSourceInterval where
  source : PointedSimplicialSet.{u}
  target : PointedSimplicialSet.{u}
  unit : source ⟶ target
  unit_anodyne : SSet.anodyneExtensions unit.right
  first : source ⟶ source
  second : source ⟶ source
  path : PointedMapping.VerticalPath (PointedObject.toPoint target)
    (first ≫ unit) (second ≫ unit)

namespace UniversalSourceInterval
variable (I : UniversalSourceInterval.{u})

/-- 同じ普遍的単位への制限は、全ての単射に対する RLP を持つ。 -/
lemma universalRestriction_rlp (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp I.unit I.unit_anodyne Z

/-- 同じ普遍的入力の全族を Kan 置換へ延長する、実際の基点固定切断。 -/
def extensionSection (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedObject.basedHom I.source Z ⟶ PointedObject.basedHom I.target Z :=
  PointedMapping.sectionOfRlp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z)
    (universalRestriction_rlp I Z)

/-- 延長した全族は、元の普遍的単位への制限で厳密に戻る。 -/
lemma extensionSection_condition (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    extensionSection I Z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z = 𝟙 _ :=
  PointedMapping.sectionOfRlp_condition _ _

/-- 一つの普遍的区間から得た、全写像空間の二つの源作用を結ぶ実区間。 -/
def interval (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint (PointedObject.basedHom I.source Z))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z) := by
  have hs : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z = extensionSection I Z ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (I.first ≫ I.unit) Z := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, ← Category.assoc,
      extensionSection_condition, Category.id_comp]
  have hr : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z = extensionSection I Z ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (I.second ≫ I.unit) Z := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, ← Category.assoc,
      extensionSection_condition, Category.id_comp]
  exact ((I.path.basedPre Z).pre (extensionSection I Z)).changeEndpoints hs hr

/-- 得た辺全体は、同じ普遍区間を前合成へ移して同じ切断へ制限したもの。 -/
lemma interval_path (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (interval I Z).path =
      ((I.path.basedPre Z).pre (extensionSection I Z)).path := rfl

/-- 普遍的単位への制限は、標的への後合成に対して厳密に自然。 -/
lemma universalRestriction_post {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    PointedObject.basedHomMap I.target v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z' =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z ≫ PointedObject.basedHomMap I.source v := by
  have h := (MonoidalClosed.pre I.unit).naturality v
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap I.target v ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z' =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z ≫ PointedObject.basedHomMap I.source v at h
  exact h

/-- 二つの標的の延長切断の比較は、同じ制限を全区間で固定できる。 -/
def extensionSectionNaturalityInterval {Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : Z ⟶ Z') :
    PointedMapping.VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z')
      (extensionSection I Z ≫ PointedObject.basedHomMap I.target v)
      (PointedObject.basedHomMap I.source v ≫ extensionSection I Z') :=
  PointedMapping.sectionNaturalityInterval _ (universalRestriction_rlp I Z)
    _ (universalRestriction_rlp I Z') _ _ (universalRestriction_post I v)

end UniversalSourceInterval
end SerrePositivity.KST.Spectra
