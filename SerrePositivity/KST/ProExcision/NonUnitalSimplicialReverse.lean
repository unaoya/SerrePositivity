module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialOpposite
public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# 非単位単体環の係数方向の順序反転

概要：非単位単体環の全ての面・退化に rev を前合成した実図式を構成する。
方針：各次数の環を保ち、反変単体射を rev で移す。
規約：KST Proposition 4.14、SW92 §1.2 の行側の実対角比較の正確化。
使われ方：係数方向と nerve 方向の反転を合わせて対角全体の SSet.op にする。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：非単位単体環の係数の単体方向の順序反転。
方針：元の環を保ち、面・退化に rev を前合成する。
規約：KST Proposition 4.14、元の環との同型は仮定しない。
使われ方：Claim 4.15 を行側の比較に適用する際の係数図式。 -/
def NonUnitalSimplicialRing.reverse (I : NonUnitalSimplicialRing.{u}) : NonUnitalSimplicialRing.{u} where
  obj k := I.obj k
  map f := I.map (SimplexCategory.rev.map f.unop).op
  map_id k := by
    rw [show (SimplexCategory.rev.map (𝟙 k).unop).op = 𝟙 k by simp]
    exact I.map_id k
  map_comp f g := by
    rw [show (SimplexCategory.rev.map (f ≫ g).unop).op =
        (SimplexCategory.rev.map f.unop).op ≫ (SimplexCategory.rev.map g.unop).op by simp]
    exact I.map_comp _ _

/-- 概要：係数の順序反転と反対環を合わせた実非単位単体環。
方針：定義済みの二つの実図式の操作を合成する。
規約：SW92 §1.2 の非可換行側の対角比較。使われ方：行側の Claim 4.15 の入力。 -/
def NonUnitalSimplicialRing.reverseOpposite (I : NonUnitalSimplicialRing.{u}) :
    NonUnitalSimplicialRing.{u} := I.reverse.mulOpposite

end SerrePositivity.KST.ProExcision
