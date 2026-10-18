module

public import SerrePositivity.KST.Descent.Axioms
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# 全次数比較と前層の導来値域への接続

## 概要
論文 (3.7) の比較を、指定された導来値域とその全次数の観測関手に対して扱う。

## 方針
値域と観測関手は引数とし、同型の retract が各次数でも同型になることを証明する。
次数付き前層との比較は自然同型として保持する。

## 規約
L9 の Sp・π_n・Tot の実構成は定義しない。観測関手が π_n であることも仮定しない。
以下の補題は任意の観測関手で成立し、L9 の実構成を接続したとき π_* に適用される。
通常の極限をホモトピー極限に置き換える仮定は含まない。

## 使われ方
補題 3.2 の比較写像の retract と、定理 3.1 の全次数 π_* という公開主張をつなぐ。
-/

@[expose] public section

universe u v w t u' v'

open CategoryTheory

namespace SerrePositivity.KST.Descent

variable {V : Type u'} [Category.{v'} V]

/-- 概要：指定された全整数次数の観測関手で同型となる射（定理 3.1、(3.7)）。
方針：各次数の関手で射を写して同型性を要求する。
規約：観測関手自体の構成や同値検出性は含めない。
使われ方：L9 の π_n を接続する前にも定式化できる全次数比較。 -/
def piIsomorphisms (observation : ℤ → V ⥤ ModuleCat.{t} ℚ) : MorphismProperty V :=
  fun _ _ f ↦ ∀ n, IsIso ((observation n).map f)

/-- 概要：値域の同型は全次数の観測で同型（論文 補題 3.2 の分裂降下の利用）。
方針：関手の同型保存を使う。
規約：逆向きの同値検出は要求しない。
使われ方：分裂余単体対象の実際の降下から π_* 比較を得る。 -/
theorem piIsomorphisms_of_isIso (observation : ℤ → V ⥤ ModuleCat.{t} ℚ)
    {X Y : V} (f : X ⟶ Y) [IsIso f] : piIsomorphisms observation f := by
  intro n
  infer_instance

/-- 概要：全次数比較は合成で閉じる（論文 定理 3.1 の比較の組み立て）。
方針：関手の合成保存と同型の合成を使う。
規約：負次数を含むすべての整数次数で主張する。
使われ方：被約化や (3.6) の比較と降下比較を合成する。 -/
theorem piIsomorphisms_comp (observation : ℤ → V ⥤ ModuleCat.{t} ℚ)
    {X Y Z : V} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : piIsomorphisms observation f) (hg : piIsomorphisms observation g) :
    piIsomorphisms observation (f ≫ g) := by
  intro n
  have := hf n
  have := hg n
  rw [(observation n).map_comp]
  infer_instance

/-- 概要：全次数で同型となる射の性質は retract で閉じる（論文 補題 3.2）。
方針：各観測関手で retract を写し、同型射の retract の同型性を使う。
規約：図式の射そのものの retract が入力であり、各対象の群の分裂だけではない。
使われ方：Čech 比較の retract から全次数の降下を引き継ぐ。 -/
instance piIsomorphisms_stableUnderRetracts
    (observation : ℤ → V ⥤ ModuleCat.{t} ℚ) :
    (piIsomorphisms observation).IsStableUnderRetracts where
  of_retract h hg n :=
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
      (h.map (observation n)) (hg n)

/-- 概要：比較写像の retract による全次数同型の移行（論文 補題 3.2）。
方針：全次数の同型性の retract 安定性を適用する。
規約：Tot の実構成はこの補題の仮定ではなく、後で実際の比較射に適用する。
使われ方：rank で正規化した transfer の図式から降下比較を得る。 -/
theorem piIsomorphisms_of_retract (observation : ℤ → V ⥤ ModuleCat.{t} ℚ)
    {X Y Z W : V} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
    (hg : piIsomorphisms observation g) : piIsomorphisms observation f :=
  MorphismProperty.of_retract h hg

/-- 概要：全次数同型を線形写像の全単射性として読み替える（定理 3.1 の公開形）。
方針：有理加群の圏で同型と全単射が一致することを各次数で使う。
規約：指定した射の像の性質であり、無関係な抽象同型の存在ではない。
使われ方：`GradedPresheaf.PiDescent` と導来値域の比較射を接続する。 -/
theorem piIsomorphisms_iff_bijective (observation : ℤ → V ⥤ ModuleCat.{t} ℚ)
    {X Y : V} (f : X ⟶ Y) :
    piIsomorphisms observation f ↔
      ∀ n, Function.Bijective (((observation n).map f).hom) := by
  simp only [piIsomorphisms, ConcreteCategory.isIso_iff_bijective]

/-- 概要：次数付き前層と導来値域の前層との自然な比較（論文 (3.5)、(3.7)）。
方針：係数ごとの値域 V の前層と、各観測次数での自然同型を保持する。
規約：V と観測関手は外部の引数。Tot・fiber・hG の存在や降下は含めない。
本構造は実現のデータであり、定理 3.1 の結論を仮定する束ではない。
使われ方：正本 D7 に従い、L9 の実構成を L8 の次数付き公開界面に接続する。 -/
structure PresheafRealization {C : Type u} [Category.{v} C] {Coefficient : Type w}
    (observation : ℤ → V ⥤ ModuleCat.{t} ℚ)
    (L : GradedPresheaf.{u, v, w, t} C Coefficient) where
  /-- 概要：係数ごとの V 値の反変前層（論文 (3.5)）。
  方針：反変関手そのものを保持する。
  規約：L9 の値域の具体的構成は外部で供給する。
  使われ方：導来図式の入力。 -/
  value : Coefficient → Cᵒᵖ ⥤ V
  /-- 概要：観測した前層と公開する次数付き前層の自然同型（論文 (3.7)）。
  方針：射に対する自然性も含む同型を保持する。
  規約：単に各対象で群が同型というデータには弱めない。
  使われ方：実際の引き戻し比較と次数付き比較の一致。 -/
  comparison : ∀ H n, value H ⋙ observation n ≅ L H n

end SerrePositivity.KST.Descent
