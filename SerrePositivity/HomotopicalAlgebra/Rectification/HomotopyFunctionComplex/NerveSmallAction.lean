module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionFunctors
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveSmallFamilies

/-!
# 中断した任意モデル源への一般化：NerveSmallAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Small whole-chain actions with both actual endpoint transports under every simplex operator。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0131][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0131
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Small whole-chain actions with both actual endpoint transports under every simplex operator
-/

@[expose] public section
universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.HomotopyFunctionComplex.NerveSmallAction
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ ResolutionArrowDiagram.Index C)
  (K : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ ResolutionArrowDiagram.fibers C))

abbrev parameter {n : ℕ} (c : ComposableArrows D n) :=
  K.obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)
abbrev center {n : ℕ} (c : ComposableArrows D n) := H.obj (c.obj (Fin.last n))
abbrev input {n : ℕ} (c : ComposableArrows D n) (Z : C) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionArrowDiagram.target C (center C H c)).resolution.obj).obj Z

/-- A whole-chain action on small resolution Hom, retaining the actual last center. -/
def action {n : ℕ} (c : ComposableArrows D n) (Z : C) (t : parameter K c ⟶ input C H c Z) :=
  ResolutionArrowActionTransport.kan C hcof hfib (center C H c) Z
    (NerveSmallFamilies.family K (H ⋙ ResolutionArrowDiagram.fibers C) a c) t

abbrev reindexChain {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) : ComposableArrows D m :=
  (SimplexCategory.toCat.map θ).toFunctor ⋙ c
abbrev operatorParameter {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  K.obj (c.obj 0) ◁ SSet.stdSimplex.{v}.map θ
abbrev prefixParameter {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) ▷
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk m)
abbrev tailMap {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  H.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))
abbrev inputMap {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  (ResolutionArrowActionFunctors.input C Z).map (tailMap C H c θ).op
abbrev outputMap {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  (ResolutionArrowActionFunctors.output C hcof hfib Z).map (tailMap C H c θ)

lemma operator {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : parameter K c ⟶ input C H c Z) :
    operatorParameter K c θ ≫ action C hcof hfib H K a c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib (center C H (reindexChain c θ)) Z
      (prefixParameter K c θ ≫ NerveSmallFamilies.family K
        (H ⋙ ResolutionArrowDiagram.fibers C) a (reindexChain c θ))
      ((operatorParameter K c θ ≫ t) ≫ inputMap C H c θ Z) ≫
        outputMap C hcof hfib H c θ Z := by
  change _ ≫ KanLiftAction.parameterized _ _ _ _ _ _ _ _ = _
  rw [KanLiftAction.parameterized_naturality, NerveSmallFamilies.family_naturality]
  exact ResolutionArrowActionTransport.kan_transport C hcof hfib (tailMap C H c θ) Z _ _

/-- When the input also reindexes, the whole action reindexes by the actual prefix and tail. -/
lemma operator_of_input {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : parameter K c ⟶ input C H c Z)
    (t' : parameter K (reindexChain c θ) ⟶ input C H (reindexChain c θ) Z)
    (ht : (operatorParameter K c θ ≫ t) ≫ inputMap C H c θ Z = prefixParameter K c θ ≫ t') :
    operatorParameter K c θ ≫ action C hcof hfib H K a c Z t =
      (prefixParameter K c θ ≫ action C hcof hfib H K a (reindexChain c θ) Z t') ≫
        outputMap C hcof hfib H c θ Z := by
  rw [operator, ht]
  exact congrArg (fun z => z ≫ outputMap C hcof hfib H c θ Z)
    (KanLiftAction.parameterized_naturality hcof hfib _ _ _ Z
      (prefixParameter K c θ) _ t').symm

omit [ModelCategory SSet.{v}] hcof hfib a in
lemma tailMap_id {n : ℕ} (c : ComposableArrows D n) :
    tailMap C H c (𝟙 (SimplexCategory.mk n)) = 𝟙 (center C H c) := by
  change H.map (c.map (𝟙 _)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

omit [ModelCategory SSet.{v}] hcof hfib a in
lemma tailMap_comp {n m l : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    tailMap C H c (σ ≫ θ) = tailMap C H (reindexChain c θ) σ ≫ tailMap C H c θ := by
  dsimp only [tailMap, reindexChain, Functor.comp_map]
  rw [← H.map_comp, ← c.map_comp]
  congr 2

omit [ModelCategory SSet.{v}] in
lemma inputMap_comp {n m l : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) (Z : C) :
    inputMap C H c (σ ≫ θ) Z = inputMap C H c θ Z ≫ inputMap C H (reindexChain c θ) σ Z := by
  change (ResolutionArrowActionFunctors.input C Z).map (tailMap C H c (σ ≫ θ)).op = _
  rw [tailMap_comp]
  exact (ResolutionArrowActionFunctors.input C Z).map_comp _ _

lemma outputMap_comp {n m l : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) (Z : C) :
    outputMap C hcof hfib H c (σ ≫ θ) Z =
      outputMap C hcof hfib H (reindexChain c θ) σ Z ≫ outputMap C hcof hfib H c θ Z := by
  change (ResolutionArrowActionFunctors.output C hcof hfib Z).map
    (tailMap C H c (σ ≫ θ)) = _
  rw [tailMap_comp]
  exact (ResolutionArrowActionFunctors.output C hcof hfib Z).map_comp _ _

end SerrePositivity.HomotopyFunctionComplex.NerveSmallAction
