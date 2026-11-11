module

public import SerrePositivity.KST.Descent.FamilyCechOver
public import SerrePositivity.KST.Descent.FamilyCechMapLocality
public import SerrePositivity.KST.Descent.LocalRankIsomorphisms

/-!
# Over 上の自然な作用の被覆族による rank 検査

## 概要
transfer の自然変換と同じ Over 上で、chart ごとの正 rank の式から元の基底での弱同値を得る。

## 方針
元の被覆族の実降下を Over へ移し、多重交叉の零番目の射影を chart への射として使う。

## 規約
Over 上の作用を元の圏上の作用へ任意に延長しない。有限積保存は前提にしない。

## 使われ方
論文 公理 (1)・(4)、補題 3.2 の transfer の合成の局所可逆性。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {Y T : FiniteTypeSchemes S}
  (q : T ⟶ Y) (c : FiniteTypeZariskiCover T)
  {V : Type v} [Category.{w} V] [Preadditive V] [Linear ℚ V]
  (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (U : V ⥤ SSet.{0})
  (a : overPresheaf (Y := Y) F ⟶ overPresheaf (Y := Y) F)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]
  [FiniteZariskiCechDescent I J (F ⋙ U)]

include I J in
/-- 概要：Over の chart 上の正 rank の作用は元の対象で弱同値（補題 3.2）。
方針：元の実降下を Over へ移し、各多重交叉の指定射影に局所 rank の式を適用する。
規約：作用は Over 上の自然変換のまま使用。使われ方：pullback と transfer の合成の局所化後の正規化。 -/
theorem overZariskiAction_weak_of_rankOverCharts
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    (rank : c.Index → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ (i : c.Index) (Z : Over Y)
      (_r : Z ⟶ familyOverObjects q c.obj c.inclusion i),
      a.app (op Z) = (rank i : ℚ) • 𝟙 ((overPresheaf (Y := Y) F).obj (op Z))) :
    weakEquivalences SSet.{0} (U.map (a.app (op (Over.mk q)))) := by
  have hA := familyOverPresheafSpace_descent q c.obj c.inclusion I J (F ⋙ U)
    (FiniteZariskiCechDescent.descent c)
  apply familyCechPresheafMap_weak_on_base (familyOverObjects q c.obj c.inclusion)
    (familyOverCover q c.obj c.inclusion) I J hcof (Functor.whiskerRight a U) hA hA
  intro n b
  let Z := familyCechTerm (familyOverObjects q c.obj c.inclusion)
    (familyOverCover q c.obj c.inclusion) n b
  have he := hlocal (b 0) Z
    (WidePullback.π (fun j ↦ familyOverCover q c.obj c.inclusion (b j)) 0)
  have : IsIso (a.app (op Z)) := by
    rw [he]
    exact (positiveRankIdentityIso _ (rank (b 0)) (positive (b 0))).isIso_hom
  exact mem_weakEquivalences (U.map (a.app (op Z)))

end SerrePositivity.KST.Descent
