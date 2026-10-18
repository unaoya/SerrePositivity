module

public import SerrePositivity.KST.Comparison.FreeDegeneracyShapeNaturality
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 自由な退化の余極限保存

概要：自由な退化の関手が全ての値宇宙の小さい余極限を保存することを証明する。
方針：各次数を評価関手の離散余極限と同定し、余極限と余極限の交換を使う。
規約：Segal 1974 Proposition 1.6 の模型比較のセルによる移送の条件。
使われ方：CellularNaturalComparison による任意の単体集合の augmentation の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：全射の形の終域の評価を並べた図式の関手は余極限を保つ。
方針：形ごとの評価へ帰着し、単体集合の余極限が次数ごとであることを使う。
規約：値宇宙の小さい余極限を対象とする。
使われ方：直和表示の右辺の余極限保存。
-/
instance freeDegeneracyShapeDiagram_preservesColimits (d : SimplexCategoryᵒᵖ) :
    PreservesColimitsOfSize.{u, u} (freeDegeneracyShapeDiagram.{u} d) := by
  apply preservesColimits_of_evaluation
  intro s
  change PreservesColimitsOfSize.{u, u}
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op s.as.degree))
  infer_instance

/--
概要：自由な退化の関手は小さい余極限を保つ。
方針：各次数の直和表示の自然同型で、評価関手と直和の余極限保存を移す。
規約：型の余極限と値宇宙の小さい添字を使う。
使われ方：標準単体上の比較を任意の単体集合へ移す。
-/
instance freeDegeneracies_preservesColimits :
    PreservesColimitsOfSize.{u, u} freeDegeneracies.{u} := by
  apply preservesColimits_of_evaluation
  intro d
  have : PreservesColimitsOfSize.{u, u} (freeDegeneracyShapeDiagram.{u} d ⋙ colim) :=
    inferInstance
  exact preservesColimits_of_natIso (freeDegeneracyShapeColimitNatIso.{u} d).symm

end SerrePositivity.KST.Comparison
