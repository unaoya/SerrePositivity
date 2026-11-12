module

public import SerrePositivity.KST.Descent.FiniteCoproductPullbacks
public import SerrePositivity.KST.Descent.CechMapLocality

/-!
# 非交和の Čech 段で異なる局所 rank の反映

## 概要
基底を覆う非交和の Čech の零番目の座標で有限成分に分け、異なる正 rank 作用の弱同値を基底へ反映する。

## 方針
各 Čech 段を零番目の座標で引き戻した有限非交和として扱い、有限積保存と実際の Čech 降下を使う。

## 規約
rank は chart ごとに異なってよい。各段のすべての座標の組への分解を仮定しない。

## 使われ方
論文 補題 3.2 の有限自由 chart 上の射影公式から有理 transfer の合成の局所可逆性を得る。
-/

@[expose] public section

noncomputable section

universe u v w t z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [FinitaryPreExtensive C]
  {V : Type w} [Category.{t} V] [Preadditive V] [Linear ℚ V]
  (F : Cᵒᵖ ⥤ V) [PreservesFiniteProducts F] (U : V ⥤ SSet.{0}) (a : F ⟶ F)
  {ι : Type z} [Finite ι] (X : ι → C) {Y : C} (g : ∐ X ⟶ Y)
  [ModelCategory SSet.{0}]
  (genI genJ : MorphismProperty SSet.{0})
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} genI genJ]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：Čech の零番目の座標での正 rank の検査は基底の作用の弱同値を反映（補題 3.2）。
方針：各段の有限引き戻し成分で同型性を反映し、元の Čech 降下で基底の射へ戻す。
規約：元の値域の同型性は局所成分だけで使い、値域関手の同型反映は要求しない。
使われ方：変動 rank の transfer の合成を実際のホモトピー比較で正規化する。 -/
theorem cechPresheafEndomorphism_weak_of_localPositiveRanks
    (hg : HasCechSpaceDescent SimplexCategory genI genJ (cechAugmentedPresheafSpace g (F ⋙ U)))
    (rank : ι → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (n : SimplexCategory) (i : ι),
      a.app (op (pullback
        (WidePullback.π (fun _ : Fin (n.len + 1) ↦ g) 0) (Sigma.ι X i))) =
        (rank i : ℚ) • 𝟙 (F.obj (op (pullback
          (WidePullback.π (fun _ : Fin (n.len + 1) ↦ g) 0) (Sigma.ι X i))))) :
    weakEquivalences SSet.{0} (U.map (a.app (op Y))) := by
  apply cechPresheafMap_weak_on_base g (Functor.whiskerRight a U) genI genJ hg hg
  intro n
  have : IsIso (a.app (op ((Arrow.mk g).cechNerve.obj (op n)))) :=
    naturalEndomorphism_isIso_of_rankOnPullbackComponents X
      (WidePullback.π (fun _ : Fin (n.len + 1) ↦ g) 0) F a rank positive (hlocal n)
  have : IsIso (U.map (a.app (op ((Arrow.mk g).cechNerve.obj (op n))))) := inferInstance
  exact mem_weakEquivalences (U.map (a.app (op ((Arrow.mk g).cechNerve.obj (op n)))))

end SerrePositivity.KST.Descent
