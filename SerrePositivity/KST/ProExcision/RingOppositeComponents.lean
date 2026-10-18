module
public import SerrePositivity.KST.ProExcision.ComponentRingMaps
public import Mathlib.Algebra.Ring.Opposite

/-!
# 反対単体環と既存の成分環の実比較

概要：各次数で積を逆転した単体的環の成分環を、成分環の反対環と実同型で比較する。
方針：台の単体的集合は op・unop の自然な実全単射で結び、積の順序反転を代表で確認する。
規約：KST Proposition 4.14、SW92 §1.2。単体方向の反転とは別の操作。
使われ方：転置を伴う ĜL の成分行列の単位条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：各次数の実反対環を取った単体的環。
方針：環準同型の op を全単体射に適用する。
規約：KST Proposition 4.14、非可換な積の逆転。使われ方：行側の周囲環の比較。 -/
def ringOppositeObject (A : SimplicialObject RingCat.{u}) : SimplicialObject RingCat.{u} where
  obj k := RingCat.of (A.obj k)ᵐᵒᵖ
  map f := RingCat.ofHom (RingHom.op (A.map f).hom)
  map_id k := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    apply MulOpposite.unop_injective
    change (A.map (𝟙 k)).hom (MulOpposite.unop x) = MulOpposite.unop x
    rw [A.map_id]
    rfl
  map_comp f g := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    apply MulOpposite.unop_injective
    change (A.map (f ≫ g)).hom (MulOpposite.unop x) =
      (A.map g).hom ((A.map f).hom (MulOpposite.unop x))
    rw [A.map_comp]
    rfl

/-- 概要：反対単体環の台の単体的集合と元の台の実同型。
方針：各次数で unop と op の実全単射を使う。
規約：KST Proposition 4.14。単体の rev ではなく係数の積だけの反転。
使われ方：成分環の比較の台。 -/
def ringOppositeSpaceIso (A : SimplicialObject RingCat.{u}) :
    Comparison.ringSpace (ringOppositeObject A) ≅ Comparison.ringSpace A :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso
      { toFun := MulOpposite.unop
        invFun := MulOpposite.op
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }) (by
      intro k l f
      apply ConcreteCategory.hom_ext
      intro x
      rfl)

/-- 概要：反対単体環の既存の成分環と成分環の反対環の実環同型。
方針：台の自然な実同型の π₀ の写像を使い、零次の代表で環演算を比較する。
規約：KST Proposition 4.14、SW92 §1.2。π₀ の定義を変更しない。
使われ方：成分での逆行列と転置の比較。 -/
def ringOppositeComponentsEquiv (A : SimplicialObject RingCat.{u}) :
    π₀ (Comparison.ringSpace (ringOppositeObject A)) ≃+* (π₀ (Comparison.ringSpace A))ᵐᵒᵖ where
  toFun x := MulOpposite.op (mapπ₀ (ringOppositeSpaceIso A).hom x)
  invFun x := mapπ₀ (ringOppositeSpaceIso A).inv (MulOpposite.unop x)
  left_inv x := by
    change mapπ₀ (ringOppositeSpaceIso A).inv (mapπ₀ (ringOppositeSpaceIso A).hom x) = x
    rw [← mapπ₀_comp_apply, Iso.hom_inv_id, mapπ₀_id_apply]
  right_inv x := by
    apply MulOpposite.unop_injective
    change mapπ₀ (ringOppositeSpaceIso A).hom
      (mapπ₀ (ringOppositeSpaceIso A).inv (MulOpposite.unop x)) = MulOpposite.unop x
    rw [← mapπ₀_comp_apply, Iso.inv_hom_id, mapπ₀_id_apply]
  map_add' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    rfl
  map_mul' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    rfl

/-- 概要：成分環の反対環比較は任意の次数の成分写像と可換。
方針：面・退化の係数写像と unop の可換性を最初の頂点で評価する。
規約：KST Proposition 4.14。使われ方：ĜL の単位条件の実比較。 -/
lemma ringOppositeComponentsEquiv_simplex (A : SimplicialObject RingCat.{u}) (n : ℕ)
    (x : (A.obj (op ⦋n⦌))ᵐᵒᵖ) :
    ringOppositeComponentsEquiv A
      (Comparison.SimplicialRing.simplexToComponents (ringOppositeObject A) n x) =
      MulOpposite.op (Comparison.SimplicialRing.simplexToComponents A n (MulOpposite.unop x)) := rfl

end SerrePositivity.KST.ProExcision
