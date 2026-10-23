module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackKanCoordinates

/-!
概要：全空間 Kan 引き戻し比較の単位上の三座標は元の指定データに一致する。
方針：二入力には単位の自然性、path 全体には選んだ path 比較の単位式を使う。
規約：元の指定 path を選び直さない。
使われ方：元の coherent な余錐と引き戻し比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：単位上の第一脚は元の第一入力の後の単位。
方針：第一脚の式に単位の自然性を合成する。
規約：元の指定第一入力。使われ方：余錐の第一脚の厳密な比較。 -/
lemma fiberwisePullbackKanComparison_unit_left :
    continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      (fiberwisePullbackKanComparison p f g ≫
        pullback.fst (intervalReplacementEndpoint (continuousKanReplacement.map f))
          (continuousKanReplacement.map g) ≫
        pullback.snd ((intervalEndpointNatTrans 0).app (continuousKanReplacement.obj H))
          (continuousKanReplacement.map f)) =
      fiberwiseIntervalPullbackLeft p f g ≫ continuousKanReplacementUnit.app E := by
  rw [fiberwisePullbackKanComparison_left, ← continuousKanReplacementUnit.naturality]
  rfl

/-- 概要：単位上の第二脚は元の第二入力の後の単位。
方針：第二脚の式に単位の自然性を合成する。
規約：元の指定第二入力。使われ方：余錐の第二脚の厳密な比較。 -/
lemma fiberwisePullbackKanComparison_unit_right :
    continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      (fiberwisePullbackKanComparison p f g ≫
        pullback.snd (intervalReplacementEndpoint (continuousKanReplacement.map f))
          (continuousKanReplacement.map g)) =
      fiberwiseIntervalPullbackRight p f g ≫ continuousKanReplacementUnit.app D := by
  rw [fiberwisePullbackKanComparison_right, ← continuousKanReplacementUnit.naturality]
  rfl

/-- 概要：単位上の全 path は元の指定 path を元の全空間の単位で写したもの。
方針：path 座標の式、単位の自然性、両端固定の path 比較の単位式を合成する。
規約：両端だけでなく全高次単体を保持。使われ方：指定された比較ホモトピーの照合。 -/
lemma fiberwisePullbackKanComparison_unit_path :
    continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      (fiberwisePullbackKanComparison p f g ≫
        pullback.fst (intervalReplacementEndpoint (continuousKanReplacement.map f))
          (continuousKanReplacement.map g) ≫
        pullback.fst ((intervalEndpointNatTrans 0).app (continuousKanReplacement.obj H))
          (continuousKanReplacement.map f)) =
      fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app H) := by
  rw [fiberwisePullbackKanComparison_path, ← Category.assoc,
    ← continuousKanReplacementUnit.naturality]
  change (fiberwiseIntervalPullbackPath p f g ≫
    continuousKanReplacementUnit.app (fiberwiseFunctorSpace p Δ[1])) ≫ _ = _
  rw [Category.assoc, fiberwiseIntervalKanComparison_unit]

end SerrePositivity.InfinityCategories.F2
