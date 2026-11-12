module

public import SerrePositivity.KST.Descent.FamilyCechLocalRanks
public import SerrePositivity.KST.Descent.FiniteZariskiCover

/-!
# 公理 (1) から実際の有限自由 chart の rank 検査へ

## 概要
構成済みの有限自由 chart の正基底の本数を、被覆族の実降下による基底の作用の検査へ接続する。

## 方針
元の有限 Zariski 被覆と正 rank を使い、各 chart 上の任意の対象での rank の式を多重交叉へ制限する。

## 規約
有限積保存や別に指定した単一被覆射の降下を前提にしない。
局所 rank の等式を射影公式から供給する工程は明示した入力として残す。

## 使われ方
論文 補題 3.2 の有限平坦 transfer の合成の局所可逆性。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) [IsFinite f.hom.left] [AlgebraicGeometry.Flat f.hom.left]
  [Surjective f.hom.left] [LocallyOfFinitePresentation f.hom.left]
  {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0}) (a : F ⟶ F)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

include I J in
/-- 概要：有限自由 chart の元の正基底の本数による局所式から基底の作用は弱同値（補題 3.2）。
方針：構成済みの有限被覆と正 rank を、公理 (1) による chart 上の対象の検査へ直接渡す。
規約：局所式は射影公式からの入力であり、有限平坦降下全体の完成とは区別する。
使われ方：元の自然な transfer の合成の、実際の空間での局所化後の正規化。 -/
theorem finiteFreeChartFamilyAction_weak
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (hlocal : ∀ (i : finiteFreeChartIndices f.hom.left) (T : FiniteTypeSchemes S)
      (_q : T ⟶ (finiteFreeChartZariskiCover f).obj i),
      a.app (op T) = ((finiteFreeChartFamily f.hom.left i.val).rank : ℚ) • 𝟙 (F.obj (op T))) :
    weakEquivalences SSet.{0} (U.map (a.app (op Y))) :=
  finiteZariskiAction_weak_of_rankOverCharts (finiteFreeChartZariskiCover f) F U a I J hcof
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).rank)
    (fun i ↦ (finiteFreeChartFamily f.hom.left i.val).positive) hlocal

end SerrePositivity.KST.Descent
