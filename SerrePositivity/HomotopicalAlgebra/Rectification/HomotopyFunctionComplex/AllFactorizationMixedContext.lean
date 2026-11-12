module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceCompatibility
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixed

/-!
# 中断した任意モデル源への一般化：AllFactorizationMixedContext

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The already selected global mixed square in the strict context diagram。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0051][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0051
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The already selected global mixed square in the strict context diagram

The one comparison family on all factorization chains, and its four
previously selected edges, are retained through the actual choice-space
isomorphism. Finite simplices still take values in the original Hom
universe. No model on the larger parameter universe is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedContext
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X : FramedResolution C} {Y V W : ResolutionObject C} (a : X' ⟶ X)
  (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

abbrev context : MixedChoiceFunctor.Context X Y :=
  (Opposite.op (Over.mk a), Under.mk (g ≫ b))

abbrev choiceSpace : SSet.{v} :=
  (MixedChoiceFunctor.functor X Y f hcof).obj (context a g b)

abbrev valueIso : choiceSpace hcof a f g b ≅
    AllFactorizationMixed.choiceSpace a.map f g b (FramedResolution.frameMap a) :=
  MixedChoiceFunctor.choiceIso X Y f hcof (context a g b)

/-- One global square, retaining the original choice on the entire large chain parameter. -/
abbrev triangle (left : Bool) :=
  AllFactorizationMixed.triangle hcof hfib a.map f g b (FramedResolution.frameMap a) left ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).inv

lemma triangle_recover (left : Bool) :
    triangle hcof hfib a f g b left ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).hom =
      AllFactorizationMixed.triangle hcof hfib a.map f g b (FramedResolution.frameMap a) left := by
  simp only [triangle, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp, Iso.inv_hom_id]
  exact Category.comp_id _

lemma triangle_AB : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hcof hfib a f g b true =
      ((AllFactorizationPost.homotopy hcof hfib (a.map.base ≫ f) g b).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapBD hcof X'.inner X.inner Y W
          a.map f (g ≫ b) (FramedResolution.frameMap a))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).inv := by
  rw [triangle, ← Category.assoc, AllFactorizationMixed.triangle_AB]

lemma triangle_BD : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hcof hfib a f g b true =
      ((AllFactorizationPre.homotopy hcof hfib a.map f g (FramedResolution.frameMap a)).h ≫
        AllFactorizationMixed.valueMap hcof a.map f g b (FramedResolution.frameMap a)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).inv := by
  rw [triangle, ← Category.assoc, AllFactorizationMixed.triangle_BD]

lemma triangle_AC : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hcof hfib a f g b false =
      (AllFactorizationMixed.chainMap g b ▷
        SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
          (AllFactorizationPre.homotopy hcof hfib a.map f (g ≫ b)
            (FramedResolution.frameMap a)).h) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).inv := by
  rw [triangle, ← Category.assoc, AllFactorizationMixed.triangle_AC]

lemma triangle_CD : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hcof hfib a f g b false =
      ((AllFactorizationPost.homotopy hcof hfib f g b).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapAC X'.inner X.inner Y W
          a.map f (g ≫ b) (FramedResolution.frameMap a))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (valueIso hcof a f g b).inv := by
  rw [triangle, ← Category.assoc, AllFactorizationMixed.triangle_CD]

lemma common_diagonal :
    AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        triangle hcof hfib a f g b true =
      AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        triangle hcof hfib a f g b false := by
  rw [triangle, triangle, ← Category.assoc, ← Category.assoc,
    AllFactorizationMixed.common_diagonal]

/-- Retain the old finite simplex in the small context space itself. -/
abbrev simplex (left : Bool) {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ choiceSpace hcof a f g b :=
  AllFactorizationMixed.simplex hcof hfib a.map f g b (FramedResolution.frameMap a) left c t ≫
    (valueIso hcof a f g b).inv

lemma simplex_naturality (left : Bool) {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof hfib a f g b left c t =
      simplex hcof hfib a f g b left (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).map θ.op t) := by
  rw [simplex, ← Category.assoc, AllFactorizationMixed.simplex_naturality]

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedContext
