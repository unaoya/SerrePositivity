module
public import SerrePositivity.KST.SConstruction.PointedLiftSpace
public import SerrePositivity.KST.SConstruction.PointedExtensionTransport

/-! # 可換正方形による持ち上げ空間の移送
概要：持ち上げの源と射影の可換正方形を全パラメーターに作用させる。
方針：点つき写像空間の前後合成を厳密な fiber に持ち上げる。
規約：指定した底の射と切断条件を全次数で保つ。
使われ方：比較逆射の入力間の混合選択空間。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping
open scoped Simplicial

/-- 持ち上げの移送は射影による後合成と厳密に可換。 -/
lemma pointedMappingTransport_post {A A' E E' B B' : PointedSimplicialSet.{u}}
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B') (p : E ⟶ B) (p' : E' ⟶ B')
    (hp : e ≫ p' = p ≫ c) :
    pointedMappingTransport a e ≫ (PointedObject.basedHomMap A' p').right =
      (PointedObject.basedHomMap A p).right ≫ pointedMappingTransport a c := by
  have h₁ : PointedObject.basedHomMap A e ≫ PointedObject.basedHomMap A p' =
      PointedObject.basedHomMap A (e ≫ p') :=
    ((PointedObject.basedHomFunctor A).map_comp e p').symm
  have h₂ : PointedObject.basedHomMap A p ≫ PointedObject.basedHomMap A c =
      PointedObject.basedHomMap A (p ≫ c) :=
    ((PointedObject.basedHomFunctor A).map_comp p c).symm
  change ((PointedObject.basedHomMap A e ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a E') ≫
      PointedObject.basedHomMap A' p').right =
    (PointedObject.basedHomMap A p ≫ PointedObject.basedHomMap A c ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a B').right
  rw [Category.assoc, prePointed_post, ← Category.assoc, h₁, hp, ← h₂, Category.assoc]

/-- 可換正方形に沿う持ち上げの全パラメーターの移送。 -/
def pointedLiftTransport {A E B A' E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (p' : E' ⟶ B') (b' : A' ⟶ B')
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B')
    (hp : e ≫ p' = p ≫ c) (hb : a ≫ b ≫ c = b') :
    pointedLiftSpace p b ⟶ pointedLiftSpace p' b' :=
  pullback.lift
    (pullback.fst (PointedObject.basedHomMap A p).right (SSet.yonedaEquiv.symm (familyVertex b)) ≫
      pointedMappingTransport a e)
    (pullback.snd (PointedObject.basedHomMap A p).right (SSet.yonedaEquiv.symm (familyVertex b))) (by
      rw [Category.assoc, pointedMappingTransport_post a e c p p' hp,
        ← Category.assoc, pullback.condition, Category.assoc]
      congr 1
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        pointedMappingTransport_vertex, hb, Equiv.apply_symm_apply])

/-- 移送は持ち上げの写像空間への射影と厳密に可換。 -/
lemma pointedLiftTransport_projection {A E B A' E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (p' : E' ⟶ B') (b' : A' ⟶ B')
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B')
    (hp : e ≫ p' = p ≫ c) (hb : a ≫ b ≫ c = b') :
    pointedLiftTransport p b p' b' a e c hp hb ≫
      pullback.fst (PointedObject.basedHomMap A' p').right (SSet.yonedaEquiv.symm (familyVertex b')) =
      pullback.fst (PointedObject.basedHomMap A p).right (SSet.yonedaEquiv.symm (familyVertex b)) ≫
        pointedMappingTransport a e := pullback.lift_fst ..

/-- 移送の頂点は実際の持ち上げの前後合成を回収する。 -/
lemma pointedLiftTransport_vertex {A E B A' E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (p' : E' ⟶ B') (b' : A' ⟶ B')
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B')
    (hp : e ≫ p' = p ≫ c) (hb : a ≫ b ≫ c = b')
    (v : (pointedLiftSpace p b) _⦋0⦌) :
    pointedLiftMap p' b'
      ((pointedLiftTransport p b p' b' a e c hp hb).app (Opposite.op ⦋0⦌) v) =
      a ≫ pointedLiftMap p b v ≫ e := by
  apply (familyVertexEquiv A' E').injective
  change familyVertex _ = familyVertex _
  rw [pointedLiftMap, familyVertex_familyMap]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pointedLiftTransport_projection p b p' b' a e c hp hb)
      (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  have hv : (pullback.fst (PointedObject.basedHomMap A p).right
      (SSet.yonedaEquiv.symm (familyVertex b))).app (Opposite.op ⦋0⦌) v =
      familyVertex (pointedLiftMap p b v) := (familyVertex_familyMap A E _).symm
  exact (congrArg ((pointedMappingTransport a e).app (Opposite.op ⦋0⦌)) hv).trans
    (pointedMappingTransport_vertex a e (pointedLiftMap p b v))

end SerrePositivity.KST.SConstruction
