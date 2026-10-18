module

public import SerrePositivity.KST.DerivedGeometry.ShortExactPullback

/-!
概要：短完全列の左端の押し出しを対向圏の引き戻しで構成する。
方針：証明済みの pullback の短完全性を対向圏で適用する。
規約：選ばれた pullback の対向として実際の対象と射を構成する。
使われ方：Stacks Lemma 19.12.4 (079M)、TT §3・§8、Toën §3.2 の acyclic 射を殺す一工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) {E : C} (p : S.X₁ ⟶ E)

/--
概要：左端を押し出した短複体を構成する。
方針：対向短複体の右端を引き戻して戻す。
規約：第一項は E、第三項は元の第三項。
使われ方：Stacks Lemma 19.12.4、TT §3 の acyclic 射の付加。
-/
def shortComplexPushout : ShortComplex C := (shortComplexPullback S.op p.op).unop

/--
概要：元の中央対象から押し出しの中央対象への射。
方針：対向の pullback の第一射影を戻す。
規約：実際の選ばれた対象間の射。
使われ方：Stacks Lemma 19.12.4、Toën §3.2 の零ホモトピーの因子化。
-/
def shortComplexPushoutOther : S.X₂ ⟶ (shortComplexPushout S p).X₂ :=
  (pullback.fst S.f.op p.op).unop

/--
概要：押し出しの構成の二つの射は元の第一項で一致する。
方針：対向の pullback の可換式を戻す。
規約：合成の向きは元の圏で記述する。
使われ方：Stacks Lemma 19.12.4、TT §3 の零ホモトピーの移送。
-/
lemma shortComplexPushout_comm :
    p ≫ (shortComplexPushout S p).f = S.f ≫ shortComplexPushoutOther S p := by
  have h : pullback.fst S.f.op p.op ≫ S.f.op = pullback.snd S.f.op p.op ≫ p.op :=
    pullback.condition
  exact congrArg Quiver.Hom.unop h.symm

/--
概要：左端を押し出した短複体は短完全。
方針：対向圏の pullback での短完全性を使う。
規約：p の単射性・全射性は不要。
使われ方：Stacks Lemma 19.12.4、TT §3・§8 の準同型の付加。
-/
lemma shortComplexPushout_shortExact (hS : S.ShortExact) : (shortComplexPushout S p).ShortExact :=
  (shortComplexPullback_shortExact S.op p.op hS.op).unop

end SerrePositivity.KST.DerivedGeometry
