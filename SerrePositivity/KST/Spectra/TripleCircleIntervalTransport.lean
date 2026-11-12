module

public import SerrePositivity.KST.Spectra.TripleCircleUniversalExchange
public import SerrePositivity.KST.Spectra.PointedRlpSection
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace

/-!
概要：一つの普遍的な交換区間を、全標的の全写像族へ同じ anodyne 制限から移す。
方針：基点固定切断で族を延長し、同じ源区間による前合成を制限する。
規約：標的ごとの成分等式から区間を選ばない。使われ方：交換符号区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.TripleCircle

/-- 同じ普遍的単位への制限は、全ての単射に対する RLP を持つ。 -/
lemma universalRestriction_rlp (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp universalUnit.{u} universalUnit_anodyne Z

/-- 同じ普遍的入力の全族を Kan 置換へ延長する、実際の基点固定切断。 -/
def extensionSection (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedObject.basedHom source.{u} Z ⟶ PointedObject.basedHom universalTarget.{u} Z :=
  PointedMapping.sectionOfRlp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z)
    (universalRestriction_rlp Z)

/-- 延長した全族は、元の普遍的単位への制限で厳密に戻る。 -/
lemma extensionSection_condition (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    extensionSection Z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z = 𝟙 _ :=
  PointedMapping.sectionOfRlp_condition _ _

/-- 一つの普遍的区間から得た、全三重円写像空間の実際の交換符号区間。 -/
def exchangeInterval (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint (PointedObject.basedHom source.{u} Z))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z) := by
  have hs : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z = extensionSection Z ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (swap.{u} ≫ universalUnit.{u}) Z := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, ← Category.assoc,
      extensionSection_condition, Category.id_comp]
  have hr : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z = extensionSection Z ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (reversal.{u} ≫ universalUnit.{u}) Z := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, ← Category.assoc,
      extensionSection_condition, Category.id_comp]
  exact ((universalExchangePath.basedPre Z).pre (extensionSection Z)).changeEndpoints hs hr

/-- 得た辺全体は、同じ普遍区間を前合成へ移して同じ切断へ制限したもの。 -/
lemma exchangeInterval_path (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (exchangeInterval Z).path =
      ((universalExchangePath.basedPre Z).pre (extensionSection Z)).path := rfl

/-- 普遍的単位への制限は、標的への後合成に対して厳密に自然。 -/
lemma universalRestriction_post {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :
    PointedObject.basedHomMap universalTarget.{u} v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z' =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z ≫ PointedObject.basedHomMap source.{u} v := by
  have h := (MonoidalClosed.pre universalUnit.{u}).naturality v
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap universalTarget.{u} v ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z' =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z ≫ PointedObject.basedHomMap source.{u} v at h
  exact h

/-- 二つの標的の延長切断の比較は、同じ制限を全区間で固定できる。 -/
def extensionSectionNaturalityInterval {Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : Z ⟶ Z') :
    PointedMapping.VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed universalUnit.{u} Z')
      (extensionSection Z ≫ PointedObject.basedHomMap universalTarget.{u} v)
      (PointedObject.basedHomMap source.{u} v ≫ extensionSection Z') :=
  PointedMapping.sectionNaturalityInterval _ (universalRestriction_rlp Z)
    _ (universalRestriction_rlp Z') _ _ (universalRestriction_post v)

end SerrePositivity.KST.Spectra.TripleCircle
