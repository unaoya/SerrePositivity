module

public import SerrePositivity.KST.Descent.EquivariantSquareComparison

/-!
# 指定降下比較と自明表現からの不変部分の比較

## 概要
幾何射の PiDescent に現れる指定比較を、比較元の自明な引き戻し表現からの
同変写像の不変部分への制限と一致させる。

## 方針
自明作用の不変部分と元の加群の同型を前合成し、固定部分の二つの記述を移す。

## 規約
全単射性を抽象同型の選択へ置き換えない。比較の値は指定された引き戻しそのもの。

## 使われ方
論文 (3.8) と中心の帰納仮定を、実際の固定部分の列の中項の比較へ入力する。
-/

@[expose] public section

universe u v w t

open CategoryTheory Representation

namespace SerrePositivity.KST.Descent.GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)

/-- 概要：指定引き戻しを自明な幾何作用の表現からの同変写像にする（論文 (3.7)）。
方針：基底上の作用の可換式を引き戻し表現へ移す。
規約：比較元も幾何的な自明作用の引き戻し表現で記述する。
使われ方：実際の正方形の固定部分の列との型の整合。 -/
def fixedPullbackIntertwining (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) :
    IntertwiningMap (L.pullbackRepresentation H n (1 : G →* Aut Y))
      (L.pullbackRepresentation H n action) :=
  (L.pullback H n f).intertwiningMap_of_isIntertwiningMap _ _
    (L.pullback_isIntertwiningMap H n f action 1
      (by intro g; simpa using over_base g)).isIntertwining

/-- 概要：指定降下比較の全単射性を固定部分の同変比較へ移す（論文 (3.7)–(3.8)）。
方針：自明作用の不変部分の同型と固定条件の同型で指定比較と一致させる。
規約：有限群の平均作用素はこの移行には不要。
使われ方：コピー側・中心側の降下を積の不変部分の比較へ渡す。 -/
theorem fixedPullbackIntertwining_bijective (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (descent : Function.Bijective (L.invariantComparison H n f action over_base)) :
    Function.Bijective (invariantMap (L.fixedPullbackIntertwining H n f action over_base)) := by
  let source := trivialInvariantsEquiv (L.pullbackRepresentation H n (1 : G →* Aut Y))
  let target := L.invariantSubmoduleEquiv H n action
  have comm :
      invariantMap (L.fixedPullbackIntertwining H n f action over_base) ∘ source.symm =
        target ∘ L.invariantComparison H n f action over_base := by
    funext x
    apply Subtype.ext
    rfl
  have composed : Function.Bijective
      (invariantMap (L.fixedPullbackIntertwining H n f action over_base) ∘ source.symm) := by
    rw [comm]
    exact target.bijective.comp descent
  exact (Function.Bijective.of_comp_iff _ source.symm.bijective).mp composed

end SerrePositivity.KST.Descent.GradedPresheaf
