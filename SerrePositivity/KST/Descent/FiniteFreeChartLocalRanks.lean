module

public import SerrePositivity.KST.Descent.FiniteZariskiCover
public import SerrePositivity.KST.Descent.CechLocalRanks

/-!
# 実際の有限自由 chart の rank 作用の局所検査

## 概要
有限平坦全射の構成済みの有限自由 chart の正 rank を、実際の Čech 段の成分の検査へ接続する。

## 方針
有限型の圏内の有限 Zariski 被覆を使い、元の選択した正基底の本数をそのまま各成分の rank とする。

## 規約
射影公式から供給する各成分の rank の等式と、Zariski の実降下は入力に明示する。
この段階で射影公式の実現や有限平坦降下全体を完成とは主張しない。

## 使われ方
論文 補題 3.2 のベクトル束の局所自明化と自然な transfer の合成の局所可逆性。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left]
  [Surjective f.hom.left] [LocallyOfFinitePresentation f.hom.left]
  {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) [PreservesFiniteProducts F]
  (U : V ⥤ SSet.{0}) (a : F ⟶ F)
  [ModelCategory SSet.{0}]
  (genI genJ : MorphismProperty SSet.{0})
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} genI genJ]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：実際の有限自由 chart の各正 rank の等式から基底の作用は弱同値（補題 3.2）。
方針：構成済みの基底と被覆を、Čech の零番目の座標による変動 rank の判定へ渡す。
規約：rank は元の chart の正基底の本数。局所 rank の等式は射影公式からの明示した入力。
使われ方：元の前層の transfer の合成を局所化後に正規化するための検査。 -/
theorem finiteFreeChartAction_weak
    (hcover : HasCechSpaceDescent SimplexCategory genI genJ
      (cechAugmentedPresheafSpace (finiteFreeChartZariskiCover f).morphism (F ⋙ U)))
    (hlocal : ∀ (n : SimplexCategory) (i : finiteFreeChartIndices f.hom.left),
      a.app (op (pullback
        (WidePullback.π (fun _ : Fin (n.len + 1) ↦ (finiteFreeChartZariskiCover f).morphism) 0)
        (Sigma.ι (finiteFreeChartZariskiCover f).obj i))) =
      ((finiteFreeChartFamily f.hom.left i.val).rank : ℚ) •
        𝟙 (F.obj (op (pullback
          (WidePullback.π (fun _ : Fin (n.len + 1) ↦ (finiteFreeChartZariskiCover f).morphism) 0)
          (Sigma.ι (finiteFreeChartZariskiCover f).obj i))))) :
    weakEquivalences SSet.{0} (U.map (a.app (op Y))) :=
  cechPresheafEndomorphism_weak_of_localPositiveRanks F U a
    (finiteFreeChartZariskiCover f).obj (finiteFreeChartZariskiCover f).morphism genI genJ hcover
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).rank)
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).positive) hlocal

end SerrePositivity.KST.Descent
