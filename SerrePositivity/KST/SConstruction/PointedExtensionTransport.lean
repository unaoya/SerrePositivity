module
public import SerrePositivity.KST.SConstruction.PointedExtensionHomotopy
public import SerrePositivity.KST.Spectra.PathNaturality

/-! # 点つき延長の選択空間の移送
概要：源の可換正方形と標的の射は延長の全パラメーター空間に作用する。
方針：点つき内部 Hom の前合成・後合成を厳密な fiber へ持ち上げる。
規約：頂点の選択をせず、元の射への制限を全次数で固定する。
使われ方：入力を動かす Kan 随伴射の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalClosed SSet
open Spectra.PointedMapping
open scoped Simplicial

/-- 点つき写像空間の源と標的を同時に動かす射。 -/
def pointedMappingTransport {B B' Z Z' : PointedSimplicialSet.{u}}
    (b : B' ⟶ B) (z : Z ⟶ Z') :
    (PointedObject.basedHom B Z).right ⟶ (PointedObject.basedHom B' Z').right :=
  (PointedObject.basedHomMap B z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b Z').right

/-- 写像空間の移送は通常の射の頂点で前合成・後合成になる。 -/
lemma pointedMappingTransport_vertex {B B' Z Z' : PointedSimplicialSet.{u}}
    (b : B' ⟶ B) (z : Z ⟶ Z') (k : B ⟶ Z) :
    (pointedMappingTransport b z).app (Opposite.op ⦋0⦌) (familyVertex k) =
      familyVertex (b ≫ k ≫ z) := by
  simp only [pointedMappingTransport, Under.comp_right, NatTrans.comp_app,
    ConcreteCategory.comp_apply, familyVertex_post, familyVertex_pre]

/-- 写像空間の移送は恒等で恒等射になる。 -/
lemma pointedMappingTransport_id (B Z : PointedSimplicialSet.{u}) :
    pointedMappingTransport (𝟙 B) (𝟙 Z) = 𝟙 _ := by
  have hp : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 B) Z = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, pre_id]
    rfl
  have hz : PointedObject.basedHomMap B (𝟙 Z) = 𝟙 _ :=
    (PointedObject.basedHomFunctor B).map_id Z
  simp only [pointedMappingTransport, hp, hz, Category.id_comp, Under.id_right]

/-- 写像空間の移送は両変数の合成を厳密に保つ。 -/
lemma pointedMappingTransport_comp {B B' B'' Z Z' Z'' : PointedSimplicialSet.{u}}
    (b : B' ⟶ B) (c : B'' ⟶ B') (z : Z ⟶ Z') (w : Z' ⟶ Z'') :
    pointedMappingTransport b z ≫ pointedMappingTransport c w =
      pointedMappingTransport (c ≫ b) (z ≫ w) := by
  have hz : PointedObject.basedHomMap B z ≫ PointedObject.basedHomMap B w =
      PointedObject.basedHomMap B (z ≫ w) :=
    ((PointedObject.basedHomFunctor B).map_comp z w).symm
  change ((PointedObject.basedHomMap B z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b Z') ≫
      (PointedObject.basedHomMap B' w ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed c Z'')).right = _
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b Z'), prePointed_post,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, ← Category.assoc, hz]
  rfl

/-- 源の可換正方形の移送は、延長を元の部分へ制限する操作と可換。 -/
lemma pointedMappingTransport_restriction
    {A B Z A' B' Z' : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (i' : A' ⟶ B') (a : A' ⟶ A) (b : B' ⟶ B) (z : Z ⟶ Z')
    (hi : a ≫ i = i' ≫ b) :
    pointedMappingTransport b z ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i' Z').right =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right ≫ pointedMappingTransport a z := by
  change ((PointedObject.basedHomMap B z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b Z') ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i' Z').right =
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z ≫ PointedObject.basedHomMap A z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z').right
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z), prePointed_post, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, hi]

/-- 延長空間の全次数を、可換正方形と標的の射に沿って移送する。 -/
def pointedExtensionTransport {A B Z A' B' Z' : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (h : A ⟶ Z) (i' : A' ⟶ B') (h' : A' ⟶ Z')
    (a : A' ⟶ A) (b : B' ⟶ B) (z : Z ⟶ Z')
    (hi : a ≫ i = i' ≫ b) (hh : a ≫ h ≫ z = h') :
    pointedExtensionSpace i h ⟶ pointedExtensionSpace i' h' :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h)) ≫
      pointedMappingTransport b z)
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h))) (by
      rw [Category.assoc, pointedMappingTransport_restriction i i' a b z hi,
        ← Category.assoc, pullback.condition, Category.assoc]
      congr 1
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        pointedMappingTransport_vertex, hh, Equiv.apply_symm_apply])

/-- 移送は延長の写像空間への射影と厳密に可換。 -/
lemma pointedExtensionTransport_projection {A B Z A' B' Z' : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (h : A ⟶ Z) (i' : A' ⟶ B') (h' : A' ⟶ Z')
    (a : A' ⟶ A) (b : B' ⟶ B) (z : Z ⟶ Z')
    (hi : a ≫ i = i' ≫ b) (hh : a ≫ h ≫ z = h') :
    pointedExtensionTransport i h i' h' a b z hi hh ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i' Z').right (SSet.yonedaEquiv.symm (familyVertex h')) =
    pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h)) ≫
      pointedMappingTransport b z := pullback.lift_fst ..

/-- 移送は実際の延長の頂点で前合成・後合成になる。 -/
lemma pointedExtensionTransport_vertex {A B Z A' B' Z' : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (h : A ⟶ Z) (i' : A' ⟶ B') (h' : A' ⟶ Z')
    (a : A' ⟶ A) (b : B' ⟶ B) (z : Z ⟶ Z')
    (hi : a ≫ i = i' ≫ b) (hh : a ≫ h ≫ z = h')
    (v : (pointedExtensionSpace i h) _⦋0⦌) :
    pointedExtensionMap i' h'
      ((pointedExtensionTransport i h i' h' a b z hi hh).app (Opposite.op ⦋0⦌) v) =
      b ≫ pointedExtensionMap i h v ≫ z := by
  apply (familyVertexEquiv B' Z').injective
  change familyVertex _ = familyVertex _
  rw [pointedExtensionMap, familyVertex_familyMap]
  have hp := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pointedExtensionTransport_projection i h i' h' a b z hi hh)
      (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hp
  change _ = (pointedMappingTransport b z).app (Opposite.op ⦋0⦌)
    ((pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h))).app _ v) at hp
  refine hp.trans ?_
  have hv : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
      (SSet.yonedaEquiv.symm (familyVertex h))).app (Opposite.op ⦋0⦌) v =
      familyVertex (pointedExtensionMap i h v) := (familyVertex_familyMap B Z _).symm
  exact (congrArg ((pointedMappingTransport b z).app (Opposite.op ⦋0⦌)) hv).trans
    (pointedMappingTransport_vertex b z (pointedExtensionMap i h v))

end SerrePositivity.KST.SConstruction
