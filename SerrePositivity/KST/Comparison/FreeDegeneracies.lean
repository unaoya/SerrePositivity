module

public import SerrePositivity.KST.Comparison.FatNormalFormEquiv
public import SerrePositivity.KST.Comparison.FatRealizationFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 自由な退化の補助模型

概要：単体集合の各行を定数単体集合として fat realization し、元の単体集合への比較を構成する。
方針：既存の具体的な fat realization と対角への行の評価を使う。
規約：Segal 1974 Proposition 1.6 の模型比較の補助。各元は全射と元の行の単体で表す。
使われ方：標準単体上の収縮から fat realization と対角の比較を証明する準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：単体集合の各次数を定数単体集合とする二重単体集合の関手。
方針：型から定数単体集合への関手を後合成する。
規約：内側の単体作用は恒等写像。
使われ方：自由な退化の模型の入力。
-/
def discreteRowsFunctor : SSet.{u} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
    (Functor.const SimplexCategoryᵒᵖ)

/--
概要：各行を定数化した二重単体集合の対角は元の単体集合と同型。
方針：各次数の恒等同値を使い、定数単体集合の内側の作用を計算する。
規約：自然同型として元の射とも両立する。
使われ方：自由な退化から元の単体集合への augmentation。
-/
def discreteRowsDiagonalIso : discreteRowsFunctor.{u} ⋙ diagonal ≅ 𝟭 SSet.{u} :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)) (fun _ => rfl)

/--
概要：自由な退化を付けた単体集合の実際の関手。
方針：各行の定数化の後に fat realization を取る。
規約：退化を新たに自由に生成した後の augmentation の可逆性は別途証明する。
使われ方：標準単体上の収縮の模型。
-/
def freeDegeneracies : SSet.{u} ⥤ SSet.{u} := discreteRowsFunctor ⋙ fatRealizationFunctor

/--
概要：自由な退化の模型から元の単体集合への自然な射。
方針：fat realization から対角への比較と、定数化した行の対角の同型を合成する。
規約：元の退化写像も使って全射による引き戻しを評価する。
使われ方：自由な退化の模型の自然な augmentation。
-/
@[kerodon 0124]
def freeDegeneraciesAugmentation : freeDegeneracies.{u} ⟶ 𝟭 SSet.{u} :=
  Functor.whiskerLeft discreteRowsFunctor fatRealizationToDiagonalNatTrans ≫
    discreteRowsDiagonalIso.hom

/--
概要：自由な退化の各次数の元は全射と元の行の単体の組で一意に表示できる。
方針：fat realization の標準形の同値をそのまま使う。
規約：標準形の行の単体は定数単体集合の元。
使われ方：頂点の追加と余分な退化の構成。
-/
def freeDegeneraciesNormalForm (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (freeDegeneracies.obj X).obj d ≃ FatNormalForm (discreteRowsFunctor.obj X) d :=
  fatNormalFormEquiv (discreteRowsFunctor.obj X) d

end SerrePositivity.KST.Comparison
