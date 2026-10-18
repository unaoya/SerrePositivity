module

public import SerrePositivity.KST.Descent.BlowupGeometry

/-!
# スキーム上の基底を保つ作用の持ち上げ

## 概要
有限型対象の構造射を保つスキームの作用を、有限型の圏内の作用に持ち上げる。

## 方針
各自己同型を Over の同型にして充満部分圏へ持ち上げる。
群の法則は忠実な忘却によって検査する。

## 規約
基底への不変性を明示的に要求する。
前層やホモトピー固定点に関する仮定は使わない。

## 使われ方
論文 定理 3.1 の中心と例外部分の群作用を、前層 L の定義域内へ移す。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {G : Type*} [Group G]

/-- 概要：有限型の圏の G 作用をスキームの G 作用へ忘却（論文 定理 3.1）。
方針：忘却関手の自己同型群上の準同型を合成する。
規約：各群元のスキームの射を変更しない。
使われ方：実際のスキームの引き戻し上で作用を構成する。 -/
def finiteTypeUnderlyingAction {X : FiniteTypeSchemes S} (action : G →* Aut X) :
    G →* Aut X.obj.left :=
  (Functor.mapAut X (finiteTypeSchemesForget S)).comp action

/-- 概要：構造射を保つスキームの自己同型を有限型の圏へ持ち上げる（論文 §3）。
方針：Over の同型を充満部分圏の同型として包む。
規約：元の自己同型と同じスキームの射。
使われ方：構造射を保つ群作用の各群元。 -/
noncomputable def finiteTypeIsoOfSchemeIso (X : FiniteTypeSchemes S)
    (e : X.obj.left ≅ X.obj.left) (over_base : e.hom ≫ X.obj.hom = X.obj.hom) : X ≅ X :=
  ObjectProperty.isoMk _ (Over.isoMk e over_base)

/-- 概要：基底を保つスキームの G 作用を有限型の圏へ持ち上げる（論文 定理 3.1）。
方針：自己同型を持ち上げ、群の法則を元のスキーム上の作用で検査する。
規約：新たな作用を選択することなく元の各射を保つ。
使われ方：引き戻しで構成した中心と例外部分の作用。 -/
noncomputable def finiteTypeActionOfSchemeAction (X : FiniteTypeSchemes S)
    (action : G →* Aut X.obj.left)
    (over_base : ∀ g, (action g).asIso.hom ≫ X.obj.hom = X.obj.hom) : G →* Aut X where
  toFun g := Aut.of (finiteTypeIsoOfSchemeIso X (action g).asIso (over_base g))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact congrArg (fun a ↦ a.asIso.hom) action.map_one
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact congrArg (fun a ↦ a.asIso.hom) (action.map_mul g h)

/-- 概要：有限型の圏へ持ち上げた作用の各射は元の射（論文 定理 3.1）。
方針：持ち上げの定義を展開する。
規約：忘却後の同一性であり、単なる共役同型ではない。
使われ方：射影の同変性を有限型の圏で証明する。 -/
@[simp] theorem finiteTypeActionOfSchemeAction_hom (X : FiniteTypeSchemes S)
    (action : G →* Aut X.obj.left)
    (over_base : ∀ g, (action g).asIso.hom ≫ X.obj.hom = X.obj.hom) (g : G) :
    (finiteTypeActionOfSchemeAction X action over_base g).asIso.hom.hom.left =
      (action g).asIso.hom := rfl

end SerrePositivity.KST.Descent
