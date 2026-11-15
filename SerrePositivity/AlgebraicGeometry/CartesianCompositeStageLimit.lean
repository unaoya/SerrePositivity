module

public import SerrePositivity.AlgebraicGeometry.CompositeStageBaseChangeLimit

/-!
概要：Cartesian な模型の合成係数による底変換の極限を、元のチャートを頂点に保つ。
方針：既存の合成係数の極限 cone を、実際の pullback 比較同型で移す。
規約：模型と元のチャートの比較を実際の射と IsPullback で入力する。
使われ方：G2 の元のチャートの重なりの開を有限段へ降ろす。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]
  (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
  {S Y X : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
  (h : c.π.app i ≫ γ = g) (a : X ⟶ Y) (x : X ⟶ c.pt) (hpb : IsPullback a x p g)

/-- 実際の Cartesian 比較で、極限 cone の頂点を元のチャート X に保つ。 -/
def cartesianCompositeStageCone : Cone (compositeStageBaseChangeDiagram D i γ p) :=
  (compositeStageBaseChangeConeWithPoint D c i γ p g h).extend hpb.isoPullback.hom

/-- 元の X を頂点に持つ同じ cone の実際の極限性。 -/
def isLimit_cartesianCompositeStageCone [IsCofiltered J] (hc : IsLimit c) :
    IsLimit (cartesianCompositeStageCone D c i γ p g h a x hpb) :=
  IsLimit.extendIso (s := compositeStageBaseChangeConeWithPoint D c i γ p g h)
    hpb.isoPullback.hom (isLimit_compositeStageBaseChangeConeWithPoint D c hc i γ p g h)

/-- 模型への射影との合成は、元のチャートの比較射そのもの。 -/
@[reassoc (attr := simp)] theorem cartesianCompositeStageCone_π_snd (j : Over i) :
    (cartesianCompositeStageCone D c i γ p g h a x hpb).π.app j ≫
      pullback.snd (D.map j.hom ≫ γ) p = a := by
  simp [cartesianCompositeStageCone, Cone.extend]

/-- 基底への射影との合成は、元の構造射と元の極限射影の合成。 -/
@[reassoc (attr := simp)] theorem cartesianCompositeStageCone_π_fst (j : Over i) :
    (cartesianCompositeStageCone D c i γ p g h a x hpb).π.app j ≫
      pullback.fst (D.map j.hom ≫ γ) p = x ≫ c.π.app j.left := by
  simp [cartesianCompositeStageCone, Cone.extend]

/-- 元のチャートを保った極限 cone の各射影も、同じ基底の射影の底変換。 -/
theorem isPullback_cartesianCompositeStageCone_π (j : Over i) :
    IsPullback ((cartesianCompositeStageCone D c i γ p g h a x hpb).π.app j)
      x (pullback.fst (D.map j.hom ≫ γ) p) (c.π.app j.left) := by
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ (cartesianCompositeStageCone_π_fst D c i γ p g h a x hpb j).symm
    (IsPullback.of_hasPullback (D.map j.hom ≫ γ) p)
  rw [cartesianCompositeStageCone_π_snd, ← Category.assoc, c.w, h]
  exact hpb.flip

end SerrePositivity.AlgebraicGeometry
