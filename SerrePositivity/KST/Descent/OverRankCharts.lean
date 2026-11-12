module

public import SerrePositivity.KST.Descent.FamilyCechOverRanks
public import SerrePositivity.KST.Descent.FiniteZariskiBaseChange

/-!
# 固定した有限 chart の rank 公式を全ての基底対象へ移す

## 概要
Over 上の自然な作用について、元の基底の一つの有限被覆での rank 公式から全対象での弱同値を得る。

## 方針
元の chart 被覆を各構造射へ実際に底変換し、第一射影で元の chart の公式へ戻す。

## 規約
chart の有限添字と正 rank は元の被覆から保持する。

## 使われ方
論文 公理 (1)・(4)、補題 3.2 の transfer の自然な合成の全対象での正規化。
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
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0})
  (a : overPresheaf (Y := Y) F ⟶ overPresheaf (Y := Y) F)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

include I J in
/-- 概要：固定 chart の正 rank の式は任意の構造射での作用の弱同値を与える（補題 3.2）。
方針：実際の被覆の底変換と元の chart への Over 射を使う。
規約：有限積保存を要求しない。使われ方：自然な transfer の全基底変更の合成の検査。 -/
theorem overZariskiAction_weak_of_fixedRankCharts
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (Z : Over Y) (_r : Z ⟶ Over.mk (c.inclusion i)),
      a.app (op Z) = (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op Z)))
    {T : FiniteTypeSchemes S} (q : T ⟶ Y) :
    weakEquivalences SSet.{0} (U.map (a.app (op (Over.mk q)))) := by
  apply overZariskiAction_weak_of_rankOverCharts q (c.baseChange q) F U a I J
    hcof rank positive
  intro i Z r
  exact hlocal i Z (r ≫ c.baseChangeOverProjection q i)

include I J in
/-- 概要：固定 chart の正 rank の式は Over 上の全ての成分で弱同値を与える（補題 3.2）。
方針：各構造射の標準対象での弱同値を、同じ構造射を持つ元の対象の指定同型で移す。
規約：自然変換の定義域を変えない。使われ方：実際の Čech 図式に適用する前層全体の正規化。 -/
theorem overZariskiAction_weak_everywhere_of_fixedRankCharts
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (Z : Over Y) (_r : Z ⟶ Over.mk (c.inclusion i)),
      a.app (op Z) = (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op Z)))
    (Z : Over Y) : weakEquivalences SSet.{0} (U.map (a.app (op Z))) := by
  have hz := overZariskiAction_weak_of_fixedRankCharts c F U a I J
    hcof rank positive hlocal Z.hom
  let e : Over.mk Z.hom ≅ Z := Over.isoMk (Iso.refl _) (by simp)
  let m := (overPresheaf (Y := Y) F).map e.hom.op
  have hm : IsIso (U.map m) := inferInstance
  have he : U.map m ≫ U.map (a.app (op (Over.mk Z.hom))) =
      U.map (a.app (op Z)) ≫ U.map m :=
    (U.map_comp _ _).symm.trans
      ((congrArg U.map (a.naturality e.hom.op)).trans (U.map_comp _ _))
  have hc := (weakEquivalences SSet.{0}).comp_mem _ _ (mem_weakEquivalences (U.map m)) hz
  rw [he] at hc
  exact (weakEquivalences SSet.{0}).of_postcomp _ _ (mem_weakEquivalences (U.map m)) hc

end SerrePositivity.KST.Descent
