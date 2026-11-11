module
public import SerrePositivity.KST.SConstruction.CompatibleFamilyComposition
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # suspension 合成の中間にある元の置換射影を移す
概要：後続円柱の源の射影を、前の族の標的の射影へ厳密に移す。
方針：豊穣合成の中間射の交換と suspension の標的自然性を使う。
規約：全時刻の同じ円柱を保ち、置換を新しく選ばない。
使われ方：後半補正の先頭の適合円柱と区間交換正方形の終端の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra

local instance suspendedMiddleTransferPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 共通パラメータの合成で、中間射を左右どちらの族へ作用させても同じである。 -/
lemma pointed_middle_comp_lift {D : SSet.{u}} {X B R Z : PointedSimplicialSet.{u}}
    (p : B ⟶ R) (a : D ⟶ (PointedObject.basedHom X B).right)
    (h : D ⟶ (PointedObject.basedHom R Z).right) :
    lift (a ≫ (PointedObject.basedHomMap X p).right) h ≫ eComp SSet X R Z =
      lift a (h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre p Z) ≫ eComp SSet X B Z := by
  let a₀ : D ⟶ (X ⟶[SSet] B) := a
  let h₀ : D ⟶ (R ⟶[SSet] Z) := h
  have he : ((a₀ ≫ eHomWhiskerLeft SSet X p) ⊗ₘ h₀) ≫ eComp SSet X R Z =
      (a₀ ⊗ₘ (h₀ ≫ eHomWhiskerRight SSet p Z)) ≫ eComp SSet X B Z := by
    rw [← tensorHom_comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_comp_middle,
      ← Category.assoc, tensorHom_comp_whiskerLeft]
  have hd := congrArg (fun q => lift (𝟙 D) (𝟙 D) ≫ q) he
  simpa only [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq,
    ← Category.assoc, familyDiagonal_tensorHom, a₀, h₀] using hd

/-- 後続円柱の suspension 源の射影を、前の同じ族の標的の射影へ移す。 -/
lemma pointed_suspension_middle_lift {D : SSet.{u}} {X B R Z : PointedSimplicialSet.{u}}
    (p : B ⟶ R) (a : D ⟶ (PointedObject.basedHom X B).right)
    (h : D ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension R) Z).right) :
    lift (a ≫ (suspensionHom X B).right)
        (h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ p) Z) ≫
      eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension B) Z =
      lift (a ≫ (PointedObject.basedHomMap X p).right ≫ (suspensionHom X R).right) h ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension R) Z := by
  have hn := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.suspensionHom_post X p
  change (PointedObject.basedHomMap X p).right ≫ (suspensionHom X R).right =
    (suspensionHom X B).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (PointedSimplicialSet.circle.{u} ◁ p)).right at hn
  rw [← pointed_middle_comp_lift]
  rw [Category.assoc, ← hn]

end SerrePositivity.KST.SConstruction
