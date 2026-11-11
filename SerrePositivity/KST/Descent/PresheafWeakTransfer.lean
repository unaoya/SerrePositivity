module

public import SerrePositivity.KST.Descent.CechWeakTransfer
public import SerrePositivity.KST.Descent.CechBaseChangeSpaces

/-!
# 元の前層の弱同値な transfer 合成からの実降下

## 概要
元の二つの前層の自然な pullback・transfer の合成が各対象で弱同値なら、指定 Čech 降下を戻す。

## 方針
元の前層の射を実際の指定増強つき空間図式の関手で写し、局所化後の正規化を適用する。

## 規約
値域の関手は同型を反映する必要がない。合成の弱同値を値域関手の像で検査する。

## 使われ方
論文 補題 3.2 の局所 rank の可逆性を基底上で貼り合わせた後の実際の transfer 移行。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X Y : C} (g : X ⟶ Y)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：各対象で弱同値な合成を持つ元の前層の射は指定降下を戻す（補題 3.2）。
方針：前層の全自然な増強図式の関手で二つの射を写し、局所化した矢の圏で正規化する。
規約：厳密な retract や有理線形性は不要。使われ方：局所 rank を持つ transfer の結論。 -/
theorem cechPresheafDescent_of_weakComposite {F G : Cᵒᵖ ⥤ SSet.{0}}
    (i : F ⟶ G) (r : G ⟶ F)
    (hcomp : ∀ Z : C, weakEquivalences SSet.{0} ((i ≫ r).app (op Z)))
    (hG : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g G)) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F) := by
  let T := presheafCosimplicialSpaces (cechOverDiagram g) (𝟭 SSet.{0})
  let ip := T.map (Functor.whiskerLeft (Over.forget Y).op i)
  let rp := T.map (Functor.whiskerLeft (Over.forget Y).op r)
  have hB := (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso (𝟭 SSet.{0}) g G)).mpr hG
  have hA := cechSpaceDescent_of_weakComposite SimplexCategory I J ip rp
    (hcomp Y) (fun n ↦ hcomp ((Arrow.mk g).cechNerve.obj (op n))) hB
  exact (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso (𝟭 SSet.{0}) g F)).mp hA

/-- 概要：任意の値域関手で弱同値になる合成を持つ前層の transfer から実降下（補題 3.2）。
方針：値域関手の合成保存で二つの自然な射を写し、空間値前層の正規化へ渡す。
規約：元の値域の加法性も値域関手の同型反映も不要。使われ方：局所 rank の検査と実際の比較の接続。 -/
theorem cechPresheafDescent_of_observedWeakComposite
    {V : Type w} [Category.{t} V] (U : V ⥤ SSet.{0})
    {F G : Cᵒᵖ ⥤ V} (i : F ⟶ G) (r : G ⟶ F)
    (hcomp : ∀ Z : C, weakEquivalences SSet.{0} (U.map ((i ≫ r).app (op Z))))
    (hG : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g (G ⋙ U))) :
    HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g (F ⋙ U)) := by
  apply cechPresheafDescent_of_weakComposite g I J
    (Functor.whiskerRight i U) (Functor.whiskerRight r U) _ hG
  intro Z
  exact Eq.mp (congrArg (fun f : U.obj (F.obj (op Z)) ⟶ U.obj (F.obj (op Z)) ↦
    weakEquivalences SSet.{0} f) (U.map_comp (i.app (op Z)) (r.app (op Z)))) (hcomp Z)

end SerrePositivity.KST.Descent
