module
public import SerrePositivity.KST.ProExcision.NerveOppositeIso
public import SerrePositivity.KST.ProExcision.MonoidReverseOpposite

/-!
# 反対モノイドの一対象圏と反対圏の nerve

概要：反対モノイドの一対象圏を元の一対象圏の反対圏に実同型で移す。
方針：射の unop と圏の op を合成し、逆を実写像として与える。
規約：KST Proposition 4.14、SW92 §1.2。乗法と射の合成の順序を区別する。
使われ方：反対モノイドの bar と nerve 方向の反転の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：反対モノイドの一対象圏から元の一対象圏の反対圏への実関手。
方針：射を unop してから圏の反対射にする。
規約：SW92 §1.2、非可換な順序を保持する。使われ方：反対 bar の実比較。 -/
def singleObjOppositeFunctor (M : Type u) [Monoid M] :
    SingleObj Mᵐᵒᵖ ⥤ (SingleObj M)ᵒᵖ where
  obj _ := op (SingleObj.star M)
  map f := (show SingleObj.star M ⟶ SingleObj.star M from MulOpposite.unop f).op

/-- 概要：反対圏から反対モノイドの一対象圏への逆関手。
方針：圏の反対射を unop してから反対モノイドへ送る。
規約：SW92 §1.2。使われ方：nerve の実比較の逆。 -/
def singleObjUnopFunctor (M : Type u) [Monoid M] :
    (SingleObj M)ᵒᵖ ⥤ SingleObj Mᵐᵒᵖ where
  obj _ := SingleObj.star Mᵐᵒᵖ
  map f := MulOpposite.op f.unop

/-- 概要：一対象圏の反対モノイド比較はモノイド準同型に自然。
方針：対象は一つであり、射で二つの順序の定義を評価する。
規約：SW92 §1.2。使われ方：係数方向の自然性。 -/
lemma singleObjOppositeFunctor_natural {M : Type u} {N : Type v}
    [Monoid M] [Monoid N] (f : M →* N) :
    (MonoidHom.op f).toFunctor ⋙ singleObjOppositeFunctor N =
      singleObjOppositeFunctor M ⋙ f.toFunctor.op := rfl

/-- 概要：反対モノイドの一対象圏の nerve と反対圏の nerve の実同型。
方針：二つの実逆関手を nerve に適用し、射の列の外延性で逆を証明する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：対角 bar の反転同型。 -/
def singleObjOppositeNerveIso (M : Type u) [Monoid M] :
    nerve (SingleObj Mᵐᵒᵖ) ≅ nerve (SingleObj M)ᵒᵖ where
  hom := nerveMap (singleObjOppositeFunctor M)
  inv := nerveMap (singleObjUnopFunctor M)
  hom_inv_id := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      exact Subsingleton.elim _ _
    · intro i j f
      rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      exact Subsingleton.elim _ _
    · intro i j f
      rfl

/-- 概要：反対モノイドと反対圏の実 nerve 同型は係数準同型に自然。
方針：各単体の射の列で二つの関手の合成を定義から比較する。
規約：SW92 §1.2。使われ方：二重単体的 bar への束ね上げ。 -/
lemma singleObjOppositeNerveIso_natural {M : Type u} {N : Type u}
    [Monoid M] [Monoid N] (f : M →* N) :
    nerveMap (MonoidHom.op f).toFunctor ≫ (singleObjOppositeNerveIso N).hom =
      (singleObjOppositeNerveIso M).hom ≫ nerveMap f.toFunctor.op := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：反対モノイドの nerve と元の nerve の順序反転の実同型。
方針：一対象圏の実比較と反対圏の nerve の反転を合成する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：係数方向も rev した対角の実比較の各行。 -/
def monoidOppositeNerveIso (M : Type u) [Monoid M] :
    nerve (SingleObj Mᵐᵒᵖ) ≅ (nerve (SingleObj M)).op :=
  singleObjOppositeNerveIso M ≪≫ nerveOppositeIso (SingleObj M)

/-- 概要：反対モノイドの nerve の反転同型は実準同型に自然。
方針：一対象圏の比較と反対 nerve の自然性を合成する。
規約：SW92 §1.2。使われ方：対角 bar の実自然同型。 -/
lemma monoidOppositeNerveIso_natural {M : Type u} {N : Type u}
    [Monoid M] [Monoid N] (f : M →* N) :
    nerveMap (MonoidHom.op f).toFunctor ≫ (monoidOppositeNerveIso N).hom =
      (monoidOppositeNerveIso M).hom ≫ SSet.opFunctor.map (nerveMap f.toFunctor) := by
  change nerveMap (MonoidHom.op f).toFunctor ≫
      ((singleObjOppositeNerveIso N).hom ≫ (nerveOppositeIso (SingleObj N)).hom) =
    ((singleObjOppositeNerveIso M).hom ≫ (nerveOppositeIso (SingleObj M)).hom) ≫ _
  rw [← Category.assoc, singleObjOppositeNerveIso_natural, Category.assoc,
    nerveOppositeIso_natural, ← Category.assoc]

end SerrePositivity.KST.ProExcision
