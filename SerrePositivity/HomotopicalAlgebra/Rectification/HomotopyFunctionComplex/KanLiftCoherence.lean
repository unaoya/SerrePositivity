module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.KanLiftAction

/-!
# 中断した任意モデル源への一般化：KanLiftCoherence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual interval comparisons for chosen source lifts。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0103][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0103
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual interval comparisons for chosen source lifts

The chosen lift of an identity or composite need not be the identity or
composite of chosen lifts. Their actions are joined by actual simplicial
intervals, with the prescribed endpoint maps. The domain is the original
resolution Hom and the codomain is the Kan replacement of the diagonal Hom.
These comparisons alone do not constitute a strict source functor.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.KanLiftCoherence
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

/-- Precomposition by the independently chosen lift, before the comparison map. -/
abbrev chosenMap (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.resolution.obj).obj Z :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (ResolutionObject.lift f).diagram).app Z

/-- An actual family of actions, parameterized by a simplicial interval. -/
abbrev intervalAction (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ ResolutionLiftSpace.obj X Y f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⨯
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z :=
  KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ e) prod.snd

lemma intervalAction_face (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ ResolutionLiftSpace.obj X Y f)
    (i : Fin 2) :
    prod.map (SSet.stdSimplex.map (SimplexCategory.δ i)) (𝟙 _) ≫
        intervalAction hcof hfib X Y f Z e =
      KanLiftAction.parameterized hcof hfib X Y f Z
        (prod.fst ≫ SSet.stdSimplex.map (SimplexCategory.δ i) ≫ e) prod.snd := by
  rw [intervalAction, KanLiftAction.parameterized_naturality]
  simp only [prod.map_fst_assoc, prod.map_snd, Category.comp_id]

/-- The entire interval family, not just its endpoints, is natural in the target. -/
lemma intervalAction_target_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {Z Z' : C} (h : Z ⟶ Z')
    (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ ResolutionLiftSpace.obj X Y f) :
    prod.map (𝟙 _) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).map h) ≫
        intervalAction hcof hfib X Y f Z' e =
      intervalAction hcof hfib X Y f Z e ≫ (KanLiftAction.targetFunctor hcof hfib X).map h := by
  rw [intervalAction, KanLiftAction.parameterized_naturality]
  simp only [prod.map_fst_assoc, Category.id_comp, prod.map_snd]
  exact KanLiftAction.parameterized_target_naturality hcof hfib X Y f h _ _

/-- Prescribed higher lift boundaries extend as families acting on the whole Hom.
The extension is chosen once, before the target Z, so all target naturality
and the specified boundary data are retained. -/
lemma boundary_extension (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (b : K ⟶ ResolutionLiftSpace.obj X Y f) :
    ∃ e : L ⟶ ResolutionLiftSpace.obj X Y f, i ≫ e = b ∧
      ∀ Z : C,
        prod.map i (𝟙 _) ≫
            KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ e) prod.snd =
          KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ b) prod.snd := by
  obtain ⟨e, he⟩ := ResolutionLiftSpace.extension hcof X Y f i b
  refine ⟨e, he, fun Z => ?_⟩
  rw [KanLiftAction.parameterized_naturality]
  simp only [prod.map_fst_assoc, prod.map_snd, Category.comp_id, he]

/-- Compare the action of the chosen lift with any strict lift over the same map.
The same interval of lifts works for every target and every simplex of its Hom. -/
lemma chosen_comparison {X Y : ResolutionObject C} (f : X ⟶ Y) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionLiftSpace.obj X Y f.base,
      ∀ Z : C,
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X Y f.base Z e =
          prod.snd ≫ chosenMap X Y f.base Z ≫ KanLiftAction.comparison hcof hfib X Z ∧
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X Y f.base Z e =
          prod.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.diagram).app Z ≫
            KanLiftAction.comparison hcof hfib X Z := by
  obtain ⟨e, hs, ht⟩ := ResolutionLiftSpace.interval hcof X Y f.base
    (ResolutionLiftSpace.ofLift (ResolutionObject.lift f.base)) (ResolutionLiftSpace.ofLift f)
  refine ⟨e, fun Z => ⟨?_, ?_⟩⟩
  · rw [intervalAction_face, hs]
    exact KanLiftAction.ofLift hcof hfib (ResolutionObject.lift f.base) Z prod.fst prod.snd
  · rw [intervalAction_face, ht]
    exact KanLiftAction.ofLift hcof hfib f Z prod.fst prod.snd

/-- The chosen lift of an identity acts homotopically as the actual identity. -/
lemma identity (X : ResolutionObject C) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionLiftSpace.obj X X (𝟙 X.base),
      ∀ Z : C,
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X X (𝟙 X.base) Z e =
          prod.snd ≫ chosenMap X X (𝟙 X.base) Z ≫ KanLiftAction.comparison hcof hfib X Z ∧
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X X (𝟙 X.base) Z e =
          prod.snd ≫ KanLiftAction.comparison hcof hfib X Z := by
  obtain ⟨e, he⟩ := chosen_comparison hcof hfib (𝟙 X)
  refine ⟨e, fun Z => ⟨(he Z).1, (he Z).2.trans ?_⟩⟩
  have hi : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (ResolutionObject.Hom.diagram (𝟙 X))).app Z = 𝟙 _ := by
    ext n x
    exact Category.id_comp x
  rw [hi, Category.id_comp]

/-- Independently lifting a composite and composing its chosen lifts give
the exact two endpoint actions, in contravariant order. -/
lemma composition (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base)
    (g : Y.base ⟶ W.base) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionLiftSpace.obj X W (f ≫ g),
      ∀ Z : C,
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X W (f ≫ g) Z e =
          prod.snd ≫ chosenMap X W (f ≫ g) Z ≫ KanLiftAction.comparison hcof hfib X Z ∧
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫
            intervalAction hcof hfib X W (f ≫ g) Z e =
          prod.snd ≫ chosenMap Y W g Z ≫ chosenMap X Y f Z ≫
            KanLiftAction.comparison hcof hfib X Z := by
  obtain ⟨e, he⟩ := chosen_comparison hcof hfib
    ((ResolutionObject.lift f : X ⟶ Y) ≫ (ResolutionObject.lift g : Y ⟶ W))
  refine ⟨e, fun Z => ⟨(he Z).1, (he Z).2.trans ?_⟩⟩
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap
        ((ResolutionObject.lift f : X ⟶ Y) ≫ (ResolutionObject.lift g : Y ⟶ W)).diagram).app Z =
      chosenMap Y W g Z ≫ chosenMap X Y f Z := by
    ext n x
    exact Category.assoc _ _ _
  rw [hc, Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.KanLiftCoherence
