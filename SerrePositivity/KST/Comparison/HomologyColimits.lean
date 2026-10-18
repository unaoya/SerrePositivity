module

public import SerrePositivity.KST.Comparison.HomologyRelative
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# 非正規化整数鎖複体の余極限保存

概要：自由整数鎖複体は単体集合の余極限を複体の余極限へ送る。
方針：各次数への評価を自由アーベル群関手との合成と同定し、次数ごとの余極限で判定する。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル濾過の準備。正規化比較は別の鎖ホモトピー同値。
使われ方：horn の pushout と余極限のホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：自由整数鎖複体の次数への評価と単体集合の次数への自由群の自然同型。
方針：交互面複体の各次数はそのまま自由群であることを使う。
規約：微分を忘れた次数ごとの比較。
使われ方：余極限保存の評価による判定。
-/
def unnormalizedIntegralChainsEvalIso (n : ℕ) :
    unnormalizedIntegralChains.{u} ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌) ⋙ AddCommGrpCat.free :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)

/--
概要：自由整数鎖複体は指定宇宙の余極限を保存する。
方針：各次数で評価関手と自由関手の余極限保存を使う。
規約：添字の対象と射の宇宙は単体集合の値宇宙以下である。
使われ方：セル添付と順序余極限の鎖複体の比較。
-/
instance unnormalizedIntegralChains_preservesColimits :
    PreservesColimitsOfSize.{u, u} unnormalizedIntegralChains.{u} where
  preservesColimitsOfShape {_J} _ :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n =>
      preservesColimitsOfShape_of_natIso (unnormalizedIntegralChainsEvalIso n).symm)

end SerrePositivity.KST.Comparison
