module

public import SerrePositivity.Archive.KST.DescentConditional.ZariskiCechLaw
public import SerrePositivity.Archive.KST.DescentConditional.CechFiniteProducts
public import SerrePositivity.Archive.KST.DescentConditional.CechMapLocality

/-!
# 有限被覆族による元の前層の射の局所検査

## 概要
被覆族の全ての多重交叉で弱同値である前層の射を、元の基底へ反映する。

## 方針
各次数の成分の弱同値を有限積で束ね、元の前層に自然な増強つき Čech 関手で比較する。

## 規約
被覆を単一の非交和射へ変更せず、前層の非交和保存も仮定しない。

## 使われ方
論文 公理 (1)、補題 3.2 の有限自由 chart での rank 作用の検査。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} [Finite ι] {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：全ての多重交叉上の弱同値は元の基底上の弱同値を反映（公理 (1)）。
方針：成分の弱同値を各段の有限積で束ね、指定増強の自然性と両側の実降下を使う。
規約：前層の非交和保存は不要。使われ方：有限局所自由 chart による自然な作用の検査。 -/
theorem familyCechPresheafMap_weak_on_base
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    {F G : Cᵒᵖ ⥤ SSet.{0}} (a : F ⟶ G)
    (hF : HasCechSpaceDescent SimplexCategory I J (familyCechSpace X cover F))
    (hG : HasCechSpaceDescent SimplexCategory I J (familyCechSpace X cover G))
    (hlocal : ∀ (n : SimplexCategory) (b : Fin (n.len + 1) → ι),
      weakEquivalences SSet.{0} (a.app (op (familyCechTerm X cover n b)))) :
    weakEquivalences SSet.{0} (a.app (op Y)) := by
  let m := (familyAugmentedCechFunctor X cover).map a
  apply cechSpaceMap_left_weak_of_descent SimplexCategory I J m hF hG
  intro n
  exact cechFiniteProduct_weak hcof
    (fun b : Fin (n.len + 1) → ι ↦ a.app (op (familyCechTerm X cover n b))) (hlocal n)

/-- 概要：公理 (1) の有限 Zariski 被覆族で前層の射を検査できる（補題 3.2）。
方針：両側の実降下を法則から供給し、被覆族の局所検査へ適用する。
規約：元の被覆族を使う。使われ方：chart ごとに異なる正 rank の作用の反映。 -/
theorem finiteZariskiPresheafMap_weak_on_base
    {S : Scheme.{u}} [IsNoetherian S] {T : FiniteTypeSchemes S}
    (c : FiniteTypeZariskiCover T)
    (hcof : cofibrations SSet.{0} = MorphismProperty.monomorphisms _)
    {F G : (FiniteTypeSchemes S)ᵒᵖ ⥤ SSet.{0}} (a : F ⟶ G)
    [FiniteZariskiCechDescent I J F] [FiniteZariskiCechDescent I J G]
    (hlocal : ∀ (n : SimplexCategory) (b : Fin (n.len + 1) → c.Index),
      weakEquivalences SSet.{0} (a.app (op (familyCechTerm c.obj c.inclusion n b)))) :
    weakEquivalences SSet.{0} (a.app (op T)) :=
  familyCechPresheafMap_weak_on_base c.obj c.inclusion I J hcof a
    (FiniteZariskiCechDescent.descent c) (FiniteZariskiCechDescent.descent c) hlocal

end SerrePositivity.KST.Descent
