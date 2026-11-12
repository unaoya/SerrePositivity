module

public import SerrePositivity.KST.Comparison.TelescopeSpan
public import SerrePositivity.KST.Comparison.SimplicialSumEquivalences

/-!
# 単体集合の順序列の telescope 関手

概要：偶数・奇数の余積の span の二重写像円筒として telescope を関手化する。
方針：成分ごとの自然変換を span の射へまとめ、円筒の関手へ合成する。
規約：Segal 1974 Lemma 1.8。順序列の通常の余極限との比較はここでは主張しない。
使われ方：各段階の自然性の四角形と、模型の不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：順序列から telescope の span を取る関手。
方針：余積の成分の式で恒等と合成を確認する。
規約：三頂点とも元の順序列の各段階から作る。
使われ方：円筒の関手との合成。
-/
def telescopeSpanFunctor : (ℕ ⥤ SSet.{u}) ⥤ (WalkingSpan ⥤ SSet.{u}) where
  obj := telescopeSpan
  map := telescopeSpanMap
  map_id F := by
    apply NatTrans.ext
    funext d
    rcases d with (_ | _ | _)
    all_goals
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
  map_comp α β := by
    apply NatTrans.ext
    funext d
    rcases d with (_ | _ | _)
    all_goals
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro x
      rfl

/--
概要：順序列の telescope を取る関手。
方針：偶数・奇数の span に二重写像円筒の関手を適用する。
規約：Segal Lemma 1.8 の実際の模型。
使われ方：段階ごとのファイバーの比較。
-/
def telescopeFunctor : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u} :=
  telescopeSpanFunctor ⋙ spanCylinderFunctor

/--
概要：偶数段から telescope への写像の自然変換。
方針：余積の成分の包含と、円筒の左端の包含を合成する。
規約：添字 n は元の順序列の段階 2n を表す。
使われ方：偶数段のホモトピー引き戻しの四角形。
-/
def telescopeEvenStage (n : ℕ) :
    (evaluation ℕ SSet.{u}).obj (2 * n) ⟶ telescopeFunctor where
  app F := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun k => F.obj (2 * k)) n ≫
    spanCylinderLeft.app (telescopeSpan F)
  naturality {F G} α := by
    change α.app (2 * n) ≫ _ = _ ≫ spanCylinderFunctor.map (telescopeSpanMap α)
    rw [Category.assoc, ← spanCylinderLeft.naturality (telescopeSpanMap α), ← Category.assoc]
    exact congrArg (fun t => t ≫ spanCylinderLeft.app (telescopeSpan G))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map (fun k => α.app (2 * k)) n).symm

/--
概要：奇数段から telescope への写像の自然変換。
方針：余積の成分の包含と、円筒の右端の包含を合成する。
規約：添字 n は元の順序列の段階 2n+1 を表す。
使われ方：奇数段のホモトピー引き戻しの四角形。
-/
def telescopeOddStage (n : ℕ) :
    (evaluation ℕ SSet.{u}).obj (2 * n + 1) ⟶ telescopeFunctor where
  app F := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun k => F.obj (2 * k + 1)) n ≫
    spanCylinderRight.app (telescopeSpan F)
  naturality {F G} α := by
    change α.app (2 * n + 1) ≫ _ = _ ≫ spanCylinderFunctor.map (telescopeSpanMap α)
    rw [Category.assoc, ← spanCylinderRight.naturality (telescopeSpanMap α), ← Category.assoc]
    exact congrArg (fun t => t ≫ spanCylinderRight.app (telescopeSpan G))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map (fun k => α.app (2 * k + 1)) n).symm

/--
概要：成分ごとの局所化同型を持つ順序列の射は telescope でも局所化同型となる。
方針：三つの余積の可逆性を円筒の関手の模型の不変性へ渡す。
規約：各段階の Kan 性や遷移射の単射性は不要。
使われ方：順序列の Kan 分解で元の telescope の四角形へ戻す。
-/
theorem telescopeFunctor_map_localized_isIso {F G : ℕ ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (telescopeFunctor.map α)) := by
  apply spanCylinderFunctor_map_localized_isIso (telescopeSpanMap α)
  rintro (_ | _ | _)
  · exact simplicialSumMap_localized_isIso _ (fun i => hα (telescopeEdgeDegree i))
  · exact simplicialSumMap_localized_isIso _ (fun n => hα (2 * n))
  · exact simplicialSumMap_localized_isIso _ (fun n => hα (2 * n + 1))

end SerrePositivity.KST.Comparison
