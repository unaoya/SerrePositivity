module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# 論文 §3 の降下：次数付き前層と比較写像の基礎

## 概要
論文 (3.5) の前層の全次数の値と、(3.7) の引き戻し比較を記述する。
本ファイルは最小公理 (1)–(8) の完成版ではなく、その値域と主張の基礎である。

## 方針
係数 `H` と整数次数 `n` ごとに有理加群値の反変関手を取る。
定理 3.1 の第 1 段の主張は、指定した比較写像が全次数で全単射になる形で定義する。

## 規約
通常の不変部分とホモトピー固定点は区別する。各次数の通常の極限を Tot と呼ばない。
Čech 降下・抽象 blowup 降下の導来構造は未実装であり、結論を公理として含めない。

## 使われ方
補題 3.2・3.3 と定理 3.1 の骨格、および K0・T2 からの (3.6) の比較の共通の入口。
原典の τ 位相による議論は、後続で Tot の Fubini・分裂降下・細分の Čech 計算に置き換える。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：基底スキーム上有限型のスキームの圏（論文 §3、(3.5)）。
方針：`Over S` の構造射が局所有限型かつ準コンパクトである対象の充満部分圏を取る。
規約：有限次元性や Noether 性はこの定義には含めず、帰納法の仮定で別に要求する。
使われ方：前層 L の幾何学的な定義域。 -/
abbrev FiniteTypeSchemes (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- 概要：係数と整数次数を持つ有理加群値の前層（論文 (3.5) の π_* 側）。
方針：各 `H`、`n : ℤ` ごとに反変関手を与え、関手の法則を利用する。
規約：`Coefficient` は係数の添字型で、実際の dg 係数の実現は別の界面で供給する。
この型だけで Tot やホモトピー引き戻しを構成したとは主張しない。
使われ方：定理 3.1 の全次数比較と有限平坦 transfer の代数的基礎。 -/
abbrev GradedPresheaf (C : Type u) [Category.{v} C] (Coefficient : Type w) :=
  Coefficient → ℤ → Cᵒᵖ ⥤ ModuleCat.{t} ℚ

namespace GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)

/-- 概要：指定した射による次数付き前層の引き戻し（論文 (3.7)）。
方針：反対圏の射に関手を適用する。
規約：値は有理加群間の線形写像。
使われ方：定理 3.1 の比較写像そのものを固定する。 -/
abbrev pullback (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (L H n).obj (op Y) →ₗ[ℚ] (L H n).obj (op X) :=
  ((L H n).map f.op).hom

/-- 概要：恒等射の引き戻しは恒等写像（論文 (3.7) の自然性）。
方針：関手の恒等射保存を使う。
規約：係数と次数は固定。
使われ方：Čech の退化射と分裂の計算。 -/
@[simp] theorem pullback_id (H : Coefficient) (n : ℤ) (X : C) :
    L.pullback H n (𝟙 X) = LinearMap.id := by
  simp [pullback]

/-- 概要：合成の引き戻しは反変順序になる（論文 補題 3.2、(3.7)）。
方針：反対圏の合成と関手の合成保存を使う。
規約：右辺ではまず `g`、次に `f` を引き戻す。
使われ方：transfer の自然性と不変部分への比較写像。 -/
@[simp] theorem pullback_comp (H : Coefficient) (n : ℤ) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    L.pullback H n (f ≫ g) = (L.pullback H n f).comp (L.pullback H n g) := by
  simp [pullback]

/-- 概要：自己同型による引き戻しで固定される部分加群（論文 (3.7)–(3.8)）。
方針：各群元について線形な固定条件を課す。
規約：固定条件では `g` と `g⁻¹` は同値であり、左作用の向きの選択に依存しない。
使われ方：全次数 π_* 版の定理 3.1 の終域。hG との比較は別に必要。 -/
def invariantSubmodule (H : Coefficient) (n : ℤ) {X : C}
    {G : Type*} [Group G] (action : G →* Aut X) : Submodule ℚ ((L H n).obj (op X)) where
  carrier := {x | ∀ g, L.pullback H n (action g).asIso.hom x = x}
  zero_mem' g := map_zero _
  add_mem' hx hy g := by simp only [map_add, hx g, hy g]
  smul_mem' a x hx g := by simp only [map_smul, hx g]

/-- 概要：基底上の自己同型に対し、引き戻した類は不変（論文 (3.7)）。
方針：`action g ≫ f = f` と反変合成を評価する。
規約：係数の作用は基底からの引き戻しとして固定する。
使われ方：抽象同型の存在ではなく、幾何学的な比較写像を主張に使う。 -/
theorem pullback_mem_invariantSubmodule (H : Coefficient) (n : ℤ) {X Y : C}
    (f : X ⟶ Y) {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) (x : (L H n).obj (op Y)) :
    L.pullback H n f x ∈ L.invariantSubmodule H n action := by
  intro g
  have h := congrArg (fun k ↦ L.pullback H n k x) (over_base g)
  simpa only [pullback_comp, LinearMap.comp_apply] using h

/-- 概要：引き戻しを不変部分に値域制限した比較（論文 (3.7)）。
方針：基底上の自己同型に対する固定性を用いる。
規約：有限性や幾何的推移性は写像の定義には不要で、降下の定理に必要。
使われ方：定理 3.1 の全次数 π_* 同型の対象となる指定写像。 -/
def invariantComparison (H : Coefficient) (n : ℤ) {X Y : C} (f : X ⟶ Y)
    {G : Type*} [Group G] (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) :
    (L H n).obj (op Y) →ₗ[ℚ] L.invariantSubmodule H n action :=
  (L.pullback H n f).codRestrict _
    (L.pullback_mem_invariantSubmodule H n f action over_base)

/-- 概要：指定比較がすべての係数・整数次数で同型になるという命題（定理 3.1、(3.7)）。
方針：線形写像の全単射性で π_* 同型を表す。
規約：これは主定理の主張の型であり、降下の証明やその結論を仮定した構造体ではない。
実際の定理では有限全射・幾何的推移性・最小公理 (1)–(8) を仮定する。
使われ方：(3.6) の自然な比較を通して支持つき K_n の主張へ移す。 -/
def PiDescent {X Y : C} (f : X ⟶ Y) {G : Type*} [Group G]
    (action : G →* Aut X) (over_base : ∀ g, (action g).asIso.hom ≫ f = f) : Prop :=
  ∀ (H : Coefficient) (n : ℤ), Function.Bijective (L.invariantComparison H n f action over_base)

end GradedPresheaf

end SerrePositivity.KST.Descent
