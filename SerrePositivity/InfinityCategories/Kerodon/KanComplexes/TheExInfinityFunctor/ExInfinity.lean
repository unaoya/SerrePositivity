module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex の反復と有限極限を保つ順序余極限

概要：Ex∞ の実際の関手を Ex の反復の余極限として構成する。
方針：各反復は右随伴なので有限極限を保ち、型の filtered colimit との交換を使う。
規約：Moss 2020 Proposition 31 の有限極限保存の部分。Kan 性と単位の anodyne 性は別項目。
使われ方：非 Kan 基底の引き戻し比較に使う置換の準備。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits

/--
概要：Ex の自然数回の反復。
方針：零回を恒等、後続を Ex との合成とする。
規約：Moss 2020 §3 の Exⁿ。
使われ方：Ex∞ の順序図式の各段階。
-/
def exIterate : ℕ → SSet.{u} ⥤ SSet.{u}
  | 0 => 𝟭 _
  | n + 1 => exIterate n ⋙ SSet.ex

/--
概要：Ex の各有限反復は有限極限を保つ。
方針：Ex の右随伴性と合成に関する保存性を使う。
規約：Moss 2020 Proposition 31 の有限段階。
使われ方：余極限と有限極限の交換。
-/
instance exIterate_preservesFiniteLimits (n : ℕ) : PreservesFiniteLimits (exIterate.{u} n) := by
  induction n with
  | zero => change PreservesFiniteLimits (𝟭 SSet.{u}); infer_instance
  | succ n ih => change PreservesFiniteLimits (exIterate n ⋙ SSet.ex); infer_instance

/--
概要：Ex の反復を単位 X→Ex(X) で繋ぐ自然数添字の関手。
方針：各反復へ最終頂点による単位を適用する。
規約：Moss 2020 §3 の X→Ex(X)→Ex²(X)→…。
使われ方：Ex∞ を対象・射の双方で作る順序図式。
-/
def exSequence : ℕ ⥤ SSet.{u} ⥤ SSet.{u} :=
  Functor.ofSequence (fun n => Functor.whiskerLeft (exIterate n) exUnit)

/--
概要：反復の列に送る関手は有限極限を保つ。
方針：自然数ごとの評価で有限反復の保存性へ帰着する。
規約：Moss 2020 Proposition 31 の finite limit と反復列の整合。
使われ方：Ex∞ の有限極限保存。
-/
instance exSequence_flip_preservesFiniteLimits : PreservesFiniteLimits exSequence.{u}.flip := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{0}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro n
  change PreservesLimitsOfShape J (exIterate n)
  infer_instance

/--
概要：Ex の反復の自然数添字の余極限としての Ex∞。
方針：各単体的集合を反復列へ送り、その余極限を取る。
規約：Moss 2020 §3。この定義だけでは Kan 性を主張しない。
使われ方：有限極限を保つ Kan 置換の候補の実関手。
-/
@[kerodon 00ZB]
def exInfinity : SSet.{u} ⥤ SSet.{u} := exSequence.flip ⋙ colim

/--
概要：構成した Ex∞ は有限極限を保つ。
方針：型の filtered colimit と有限極限の交換を、単体次数ごとに適用する。
規約：Moss 2020 Proposition 31 の有限極限保存。
使われ方：引き戻しの比較に必要な厳密な有限極限保存。
-/
instance exInfinity_preservesFiniteLimits : PreservesFiniteLimits exInfinity.{u} := by
  have h : PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{0}
    intro J _ _
    infer_instance
  dsimp only [exInfinity]
  infer_instance

/--
概要：Ex の各反復から Ex∞ への余極限の標準射。
方針：反復列の余極限余錐の成分を使う。
規約：Moss 2020 §3 の順序余極限の構造射。
使われ方：単位と有限段階への因子化。
-/
def exInfinityStage (n : ℕ) : exIterate.{u} n ⟶ exInfinity where
  app X := colimit.ι (exSequence.flip.obj X) n
  naturality _X _Y f := (colimit.ι_map (exSequence.flip.map f) n).symm

/--
概要：恒等関手から Ex∞ への標準写像。
方針：反復の零段階からの標準射を取る。
規約：Moss 2020 Corollary 30 の写像の定義。anodyne 性は別に証明する。
使われ方：引き戻しと両立する Kan 置換の単位の候補。
-/
@[kerodon 00ZB]
def exInfinityUnit : 𝟭 SSet.{u} ⟶ exInfinity := exInfinityStage 0

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
