module

public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import SerrePositivity.KST.Descent.FiniteTypeAction
public import SerrePositivity.KST.Descent.PullbackAction

/-!
# 閉中心の引き戻しの有限型の圏内の作用

## 概要
閉中心の引き戻しに構成したスキームの作用を有限型の圏へ持ち上げ、両射影を同変にする。

## 方針
引き戻しの第一射影の同変性から、引き戻しの構造射の保存を導く。
スキームの群作用を持ち上げる一般補題に適用する。

## 規約
閉中心の被約性を要求しない。
基底の作用が非自明でも、cospan の二射が同変なら構成できる。

## 使われ方
論文 定理 3.1 の中心 V ×_B Z と例外部分 W ×_V (V ×_B Z) の群作用。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y Z : FiniteTypeSchemes S} {G : Type*} [Group G]
variable (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
variable (actionY : G →* Aut Y) (actionZ : G →* Aut Z) (actionX : G →* Aut X)
variable (equivariant_f : ∀ g, (actionY g).asIso.hom ≫ f = f ≫ (actionX g).asIso.hom)
variable (equivariant_i : ∀ g, (actionZ g).asIso.hom ≫ i = i ≫ (actionX g).asIso.hom)

/-- 概要：閉中心の引き戻しに誘導されるスキームの作用（論文 定理 3.1）。
方針：cospan の作用と同変式をスキームへ忘却して引き戻す。
規約：源のスキームは構成済みの実際の引き戻し。
使われ方：有限型の圏内への持ち上げ。 -/
noncomputable def closedPullbackRawAction : G →* Aut (closedImmersionPullback f i).obj.left :=
  pullbackAction f.hom.left i.hom.left (finiteTypeUnderlyingAction actionY)
    (finiteTypeUnderlyingAction actionZ) (finiteTypeUnderlyingAction actionX)
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_f g))
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_i g))

/-- 概要：閉中心の引き戻しのスキームの作用は構造射を保つ（論文 定理 3.1）。
方針：第一射影の同変性と Y の基底上の作用を合成する。
規約：基底 S 上の射であることを実際に確認する。
使われ方：作用の有限型の圏内への持ち上げ。 -/
theorem closedPullbackRawAction_over_base (g : G) :
    (closedPullbackRawAction f i actionY actionZ actionX equivariant_f equivariant_i g).asIso.hom ≫
        (closedImmersionPullback f i).obj.hom = (closedImmersionPullback f i).obj.hom := by
  have h := pullbackAction_fst f.hom.left i.hom.left (finiteTypeUnderlyingAction actionY)
    (finiteTypeUnderlyingAction actionZ) (finiteTypeUnderlyingAction actionX)
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_f g))
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_i g)) g
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ Y.obj.hom) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k ↦ pullback.fst f.hom.left i.hom.left ≫ k)
          (actionY g).asIso.hom.hom.w)))

/-- 概要：閉中心の引き戻しの有限型の圏内の G 作用（論文 定理 3.1）。
方針：スキームの作用と構造射の保存を一般の持ち上げ補題に適用する。
規約：実際の引き戻しのスキーム構造を保つ。
使われ方：同変な軌道正方形の四頂点。 -/
noncomputable def closedPullbackAction : G →* Aut (closedImmersionPullback f i) :=
  finiteTypeActionOfSchemeAction (closedImmersionPullback f i)
    (closedPullbackRawAction f i actionY actionZ actionX equivariant_f equivariant_i)
    (closedPullbackRawAction_over_base f i actionY actionZ actionX equivariant_f equivariant_i)

/-- 概要：閉中心の引き戻しの第一射影は有限型の圏内で同変（論文 定理 3.1）。
方針：スキームへ忘却して第一射影の指定可換式を使う。
規約：正方形の上辺そのものの同変性。
使われ方：前層 L の制限の同変性。 -/
theorem closedPullbackAction_fst (g : G) :
    (closedPullbackAction f i actionY actionZ actionX equivariant_f equivariant_i g).asIso.hom ≫
        (closedImmersionSquare f i).f₁₂ =
      (closedImmersionSquare f i).f₁₂ ≫ (actionY g).asIso.hom := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact pullbackAction_fst f.hom.left i.hom.left (finiteTypeUnderlyingAction actionY)
    (finiteTypeUnderlyingAction actionZ) (finiteTypeUnderlyingAction actionX)
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_f g))
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_i g)) g

/-- 概要：閉中心の引き戻しの第二射影は有限型の圏内で同変（論文 定理 3.1）。
方針：スキームへ忘却して第二射影の指定可換式を使う。
規約：正方形の左辺そのものの同変性。
使われ方：前層 L の制限の差の同変性。 -/
theorem closedPullbackAction_snd (g : G) :
    (closedPullbackAction f i actionY actionZ actionX equivariant_f equivariant_i g).asIso.hom ≫
        (closedImmersionSquare f i).f₁₃ =
      (closedImmersionSquare f i).f₁₃ ≫ (actionZ g).asIso.hom := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact pullbackAction_snd f.hom.left i.hom.left (finiteTypeUnderlyingAction actionY)
    (finiteTypeUnderlyingAction actionZ) (finiteTypeUnderlyingAction actionX)
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_f g))
    (fun g ↦ congrArg (fun k ↦ k.hom.left) (equivariant_i g)) g

end SerrePositivity.KST.Descent
