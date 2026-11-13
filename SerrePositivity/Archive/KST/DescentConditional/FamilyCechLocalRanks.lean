module

public import SerrePositivity.Archive.KST.DescentConditional.FamilyCechMapLocality
public import SerrePositivity.KST.Descent.LocalRankIsomorphisms

/-!
# 被覆族の各交叉での異なる正 rank の作用

## 概要
有限 Zariski 被覆族の交叉で成分ごとに異なる正 rank 倍となる自然な作用を、元の基底へ反映する。

## 方針
多重交叉の零番目の座標の成分の正 rank で逆を構成し、公理 (1) の被覆族の局所検査へ渡す。

## 規約
元の前層や値域関手の有限積保存を要求しない。局所 rank の等式は射影公式からの明示した入力。

## 使われ方
論文 補題 3.2 の有限自由 chart と transfer の合成の可逆性。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {Y : FiniteTypeSchemes S}
  (c : FiniteTypeZariskiCover Y)
  {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0}) (a : F ⟶ F)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

include I J in
/-- 概要：各被覆族 Čech 段の正 rank 作用は元の基底で弱同値（補題 3.2）。
方針：零番目の成分の正 rank 倍の指定逆を元の値域で構成し、空間へ写して公理 (1) で反映する。
規約：有限積保存は前提にしない。使われ方：有限自由 chart の射影公式から元の transfer の正規化。 -/
theorem familyCechAction_weak_of_localPositiveRanks
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (n : SimplexCategory) (b : Fin (n.len + 1) → c.Index),
      a.app (op (familyCechTerm c.obj c.inclusion n b)) =
        (rank (b 0) : ℚ) • 𝟙 (F.obj (op (familyCechTerm c.obj c.inclusion n b)))) :
    weakEquivalences SSet.{0} (U.map (a.app (op Y))) := by
  apply finiteZariskiPresheafMap_weak_on_base I J c hcof (Functor.whiskerRight a U)
  intro n b
  have : IsIso (a.app (op (familyCechTerm c.obj c.inclusion n b))) := by
    rw [hlocal n b]
    exact (positiveRankIdentityIso _ (rank (b 0)) (positive (b 0))).isIso_hom
  exact mem_weakEquivalences (U.map (a.app (op (familyCechTerm c.obj c.inclusion n b))))

include I J in
/-- 概要：各 chart 上の任意の対象の正 rank の式で基底の作用を検査できる（補題 3.2）。
方針：各多重交叉の零番目の射影を chart への構造射として使う。
規約：rank は chart ごとに異なってよい。使われ方：底変換で保たれる局所自由基底の rank 公式。 -/
theorem finiteZariskiAction_weak_of_rankOverCharts
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (T : FiniteTypeSchemes S) (_q : T ⟶ c.obj i),
      a.app (op T) = (rank i : ℚ) • 𝟙 (F.obj (op T))) :
    weakEquivalences SSet.{0} (U.map (a.app (op Y))) := by
  apply familyCechAction_weak_of_localPositiveRanks c F U a I J hcof rank positive
  intro n b
  exact hlocal (b 0) (familyCechTerm c.obj c.inclusion n b)
    (WidePullback.π (fun j ↦ c.inclusion (b j)) 0)

end SerrePositivity.KST.Descent
