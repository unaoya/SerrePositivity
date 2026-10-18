module

public import SerrePositivity.KST.Descent.BlowupGeometry
public import Mathlib.AlgebraicGeometry.Limits

/-!
# 同型射と空の基底の全次数降下

## 概要
引き戻しが全次数で全単射な場合の指定降下を示し、同型射と空の基底へ適用する。

## 方針
指定比較の値域制限を扱い、前層の同型保存と空スキームへの射の同型性を使う。

## 規約
前層の空対象での値を零とする公理は追加しない。

## 使われ方
論文 定理 3.1 の次元帰納と有限閉被覆の空の場合。
-/

@[expose] public section

universe u v w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：全次数で全単射な引き戻しは指定降下比較も全単射（論文 定理 3.1）。
方針：不変部分への値域制限に、元の全単射性を適用する。
規約：引き戻しは指定射そのもので、作用はその射の基底上にある。
使われ方：同型の場合の降下の基礎。 -/
theorem GradedPresheaf.piDescent_of_pullback_bijective
    {C : Type u} [Category.{v} C] {Coefficient : Type w}
    (L : GradedPresheaf.{u, v, w, t} C Coefficient) {X Y : C}
    (f : X ⟶ Y) {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (bijective : ∀ H n, Function.Bijective (L.pullback H n f)) :
    L.PiDescent f action over_base := by
  intro H n
  constructor
  · intro x y h
    exact (bijective H n).1 (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (bijective H n).2 y.val
    exact ⟨x, Subtype.ext hx⟩

/-- 概要：同型射は全次数の指定降下を満たす（論文 定理 3.1）。
方針：前層の同型保存から引き戻しの全単射性を得る。
規約：係数と全整数次数を保持し、群の有限性を要求しない。
使われ方：空の基底と同型による帰納の端点。 -/
theorem GradedPresheaf.piDescent_of_isIso
    {C : Type u} [Category.{v} C] {Coefficient : Type w}
    (L : GradedPresheaf.{u, v, w, t} C Coefficient) {X Y : C}
    (f : X ⟶ Y) [IsIso f] {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) : L.PiDescent f action over_base := by
  apply L.piDescent_of_pullback_bijective f action over_base
  intro H n
  exact ConcreteCategory.bijective_of_isIso ((L H n).map f.op)

/-- 概要：空の終域への有限型の圏内の射は同型（論文 定理 3.1）。
方針：スキームの空対象の同型性を使い、二段の忘却の同型反映で戻す。
規約：元の指定射について同型性を証明する。
使われ方：空の基底に対する帰納の始点。 -/
theorem finiteType_isIso_of_empty_target {S : Scheme.{u}} {X Y : FiniteTypeSchemes S}
    (f : X ⟶ Y) [IsEmpty Y.obj.left] : IsIso f := by
  let : (finiteTypeSchemesForget S).ReflectsIsomorphisms :=
    inferInstanceAs ((ObjectProperty.ι
      (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙
        Over.forget S).ReflectsIsomorphisms)
  let : IsIso ((finiteTypeSchemesForget S).map f) := inferInstanceAs (IsIso f.hom.left)
  exact isIso_of_reflects_iso f (finiteTypeSchemesForget S)

/-- 概要：空の基底への射は全次数の指定降下を満たす（論文 定理 3.1）。
方針：有限型の圏内の指定射の同型性を示して同型の場合を適用する。
規約：前層の降下公理や空の値を追加仮定にしない。
使われ方：有限な整成分の被覆が空の場合の帰納。 -/
theorem GradedPresheaf.piDescent_of_empty_target {S : Scheme.{u}}
    {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) [IsEmpty Y.obj.left]
    {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) : L.PiDescent f action over_base := by
  let := finiteType_isIso_of_empty_target f
  exact L.piDescent_of_isIso f action over_base

end SerrePositivity.KST.Descent
