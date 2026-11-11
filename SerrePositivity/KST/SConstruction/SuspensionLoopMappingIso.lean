module
public import SerrePositivity.KST.Spectra.SuspensionLoop
public import SerrePositivity.KST.Spectra.SpectrumMorphisms
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-! # Suspension–loop 随伴の写像空間上の同型
概要：元の suspension–loop 随伴を全単体次数の点つき写像空間へ延長する。
方針：閉モノイダル構造の内部 curry 同型を円との smash に適用する。
規約：Kan 性を仮定せず、元の suspension と loop の模型を保持する。
使われ方：全入力単体の Ω 比較を suspension 構造射へ移すための随伴界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra
open scoped Simplicial

/-- 点つき閉構造の右随伴は、具体的な基点固定内部 Hom 関手そのもの。 -/
lemma pointedMappingIhom_eq_basedHomFunctor (X : PointedSimplicialSet.{u}) :
    ihom X = PointedObject.basedHomFunctor X := rfl

/-- 内部 curry は、元の通常の射の curry を厳密に回収する。 -/
lemma suspensionLoopMapping_curry' {X Y : PointedSimplicialSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ⟶ Y) :
    MonoidalClosed.curry' f ≫ ihomCurry PointedSimplicialSet.circle.{u} X Y =
      MonoidalClosed.curry' (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y f) := by
  change curry' f ≫ ihomCurry PointedSimplicialSet.circle.{u} X Y = curry' (curry f)
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_natural_left, uncurry_ihomCurry]
  rw [← curry_natural_left]
  conv_rhs => rw [curry', uncurry_curry]
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
  change PointedSimplicialSet.circle.{u} ◁ (X ◁ curry' f) ≫
      (α_ PointedSimplicialSet.circle.{u} X _).inv ≫
        (ihom.ev (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).app Y =
    PointedSimplicialSet.circle.{u} ◁ (ρ_ X).hom ≫ f
  rw [associator_inv_naturality_right_assoc,
    MonoidalClosed.whiskerLeft_curry'_ihom_ev_app]
  rw [rightUnitor_tensor_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 元の suspension と loop の間の、点つき内部 Hom の実際の同型。 -/
def suspensionLoopPointedMappingIso (X Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y ≅
      PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  ihomCurryIso PointedSimplicialSet.circle.{u} X Y

/-- 基点固定写像空間の全単体次数での suspension–loop 同型。 -/
def suspensionLoopMappingIso (X Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y).right ≅
      (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right :=
  (Under.forget _).mapIso (suspensionLoopPointedMappingIso X Y)

/-- 写像空間の同型は頂点で元の随伴の像そのものを返す。 -/
lemma suspensionLoopMappingIso_vertex {X Y : PointedSimplicialSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ⟶ Y) :
    (suspensionLoopMappingIso X Y).hom.app _
        (pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y f) =
      pointedHomVertexEquiv X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y f) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, MonoidalClosed.curryHomEquiv']
  change (ihomCurry PointedSimplicialSet.circle.{u} X Y).right.app _
      (PointedSimplicialSet.unitVertexEquiv _ (curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, suspensionLoopMapping_curry']
  rfl

/-- 標的での任意の点つき射について、内部 curry は自然。 -/
lemma suspensionLoopPointedMappingIso_post {X Y Z : PointedSimplicialSet.{u}}
    (g : Y ⟶ Z) :
    (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map g ≫ (suspensionLoopPointedMappingIso X Z).hom =
      (suspensionLoopPointedMappingIso X Y).hom ≫
        (ihom X).map ((ihom PointedSimplicialSet.circle.{u}).map g) := by
  change (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map g ≫ ihomCurry PointedSimplicialSet.circle.{u} X Z =
    ihomCurry PointedSimplicialSet.circle.{u} X Y ≫
      (ihom X).map ((ihom PointedSimplicialSet.circle.{u}).map g)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_ihomCurry,
    uncurry_ihomCurry, ← curry_natural_left, ← curry_natural_right]
  congr 1
  rw [associator_inv_naturality_right_assoc]
  exact congrArg (fun k => (α_ PointedSimplicialSet.circle.{u} X _).inv ≫ k)
    ((ihom.ev (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).naturality g)

/-- 源での任意の点つき射についても、内部 curry は自然。 -/
lemma suspensionLoopPointedMappingIso_pre {X X' Y : PointedSimplicialSet.{u}}
    (f : X ⟶ X') :
    (MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f)).app Y ≫
        (suspensionLoopPointedMappingIso X Y).hom =
      (suspensionLoopPointedMappingIso X' Y).hom ≫
        (MonoidalClosed.pre f).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) := by
  change (MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f)).app Y ≫
      ihomCurry PointedSimplicialSet.circle.{u} X Y =
    ihomCurry PointedSimplicialSet.circle.{u} X' Y ≫
      (MonoidalClosed.pre f).app ((ihom PointedSimplicialSet.circle.{u}).obj Y)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_ihomCurry,
    uncurry_ihomCurry, ← curry_natural_left]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
  rw [associator_inv_naturality_right_assoc, id_tensor_pre_app_comp_ev,
    associator_inv_naturality_middle_assoc]

/-- 全単体次数での標的自然性。 -/
lemma suspensionLoopMappingIso_post {X Y Z : PointedSimplicialSet.{u}}
    (g : Y ⟶ Z) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map g).right ≫ (suspensionLoopMappingIso X Z).hom =
      (suspensionLoopMappingIso X Y).hom ≫
        ((ihom X).map ((ihom PointedSimplicialSet.circle.{u}).map g)).right :=
  congrArg Under.Hom.right (suspensionLoopPointedMappingIso_post (X := X) g)

/-- 全単体次数での源自然性。 -/
lemma suspensionLoopMappingIso_pre {X X' Y : PointedSimplicialSet.{u}}
    (f : X ⟶ X') :
    ((MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f)).app Y).right ≫
        (suspensionLoopMappingIso X Y).hom =
      (suspensionLoopMappingIso X' Y).hom ≫
        ((MonoidalClosed.pre f).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right :=
  congrArg Under.Hom.right (suspensionLoopPointedMappingIso_pre (Y := Y) f)

/-- 逆の写像空間同型も、頂点で元の suspension 構造射を厳密に回収する。 -/
lemma suspensionLoopMappingIso_inv_vertex {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :
    (suspensionLoopMappingIso X Y).inv.app _
        (pointedHomVertexEquiv X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f) =
      pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y).symm f) := by
  have h := congrArg ((suspensionLoopMappingIso X Y).inv.app (Opposite.op ⦋0⦌))
    (suspensionLoopMappingIso_vertex ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X Y).symm f))
  simpa only [Equiv.apply_symm_apply, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, ConcreteCategory.id_apply] using h.symm

/-- 逆随伴の全単体次数での標的自然性。 -/
lemma suspensionLoopMappingIso_inv_post {X Y Z : PointedSimplicialSet.{u}}
    (g : Y ⟶ Z) :
    (suspensionLoopMappingIso X Y).inv ≫ ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map g).right =
      ((ihom X).map ((ihom PointedSimplicialSet.circle.{u}).map g)).right ≫
        (suspensionLoopMappingIso X Z).inv := by
  apply (cancel_mono (suspensionLoopMappingIso X Z).hom).mp
  rw [Category.assoc, suspensionLoopMappingIso_post, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 逆随伴の全単体次数での源自然性。 -/
lemma suspensionLoopMappingIso_inv_pre {X X' Y : PointedSimplicialSet.{u}}
    (f : X ⟶ X') :
    (suspensionLoopMappingIso X' Y).inv ≫
        ((MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f)).app Y).right =
      ((MonoidalClosed.pre f).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right ≫
        (suspensionLoopMappingIso X Y).inv := by
  apply (cancel_mono (suspensionLoopMappingIso X Y).hom).mp
  rw [Category.assoc, suspensionLoopMappingIso_pre, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- パラメータ族の前合成の厳密な回収式を、逆随伴で全次数同時に移す。 -/
lemma suspensionLoopMappingFamily_pre {P Q : SSet.{u}}
    {X X' Y : PointedSimplicialSet.{u}} (f : X ⟶ X')
    (s : Q ⟶ (PointedObject.basedHom X' (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right)
    (t : P ⟶ (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) (j : Q ⟶ P)
    (h : j ≫ t = s ≫ ((MonoidalClosed.pre f).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) :
    j ≫ (t ≫ (suspensionLoopMappingIso X Y).inv) =
      (s ≫ (suspensionLoopMappingIso X' Y).inv) ≫
        ((MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f)).app Y).right := by
  rw [← Category.assoc, h, Category.assoc, ← suspensionLoopMappingIso_inv_pre,
    Category.assoc]

/-- 等化子による具体的な制限を用いる族についても、逆随伴は回収式を保つ。 -/
lemma suspensionLoopMappingFamily_prePointed {P Q : SSet.{u}}
    {X X' Y : PointedSimplicialSet.{u}} (f : X ⟶ X')
    (s : Q ⟶ (PointedObject.basedHom X' (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right)
    (t : P ⟶ (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) (j : Q ⟶ P)
    (h : j ≫ t = s ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) :
    j ≫ (t ≫ (suspensionLoopMappingIso X Y).inv) =
      (s ≫ (suspensionLoopMappingIso X' Y).inv) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedSimplicialSet.circle.{u} ◁ f) Y).right := by
  have hp := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))
  have h' := h.trans (congrArg (fun k => s ≫ k) hp)
  have hc := suspensionLoopMappingFamily_pre f s t j h'
  have hq := congrArg Under.Hom.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre (PointedSimplicialSet.circle.{u} ◁ f) Y)
  exact hc.trans (congrArg (fun k => (s ≫ (suspensionLoopMappingIso X' Y).inv) ≫ k) hq.symm)

end SerrePositivity.KST.SConstruction
