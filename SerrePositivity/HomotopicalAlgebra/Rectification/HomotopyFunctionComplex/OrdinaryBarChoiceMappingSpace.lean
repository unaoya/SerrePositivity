module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceMappingSpace

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual simplicial mapping spaces of relative bar-action lifts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0143][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0143
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual simplicial mapping spaces of relative bar-action lifts

The map to discrete base arrows has all-monomorphism right lifting.
Composition and units are strict on the auxiliary mapping spaces, without
asserting a strict section over the original base category.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def vertex (n : SimplexCategoryᵒᵖ) (a : Cᵒᵖ × C) :
    OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
      (SSet.stdSimplex.{max u v}.obj n.unop) := ⟨a⟩

def space (a b : Cᵒᵖ × C) : SSet.{max u v} where
  obj n := vertex hcof hfib n a ⟶ vertex hcof hfib n b
  map θ := ↾fun f => (OrdinaryBarChoiceCategory.reindex hcof hfib
    (SSet.stdSimplex.map θ.unop)).map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply OrdinaryBarChoiceCategory.hom_ext hcof hfib
    · rfl
    · change RelativeChoiceSpace.family _ _ (SSet.stdSimplex.map (𝟙 n.unop) ≫ f.extension) = _
      rw [CategoryTheory.Functor.map_id SSet.stdSimplex, Category.id_comp]
      rfl
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply OrdinaryBarChoiceCategory.hom_ext hcof hfib
    · rfl
    · change RelativeChoiceSpace.family _ _
        (SSet.stdSimplex.map (φ.unop ≫ θ.unop) ≫ f.extension) =
          RelativeChoiceSpace.family _ _
            (SSet.stdSimplex.map φ.unop ≫ (SSet.stdSimplex.map θ.unop ≫ f.extension))
      rw [SSet.stdSimplex.map_comp, Category.assoc]

abbrev labels (a b : Cᵒᵖ × C) := ULift.{max u v} (a ⟶ b)
abbrev fibers (a b : Cᵒᵖ × C) (f : labels a b) := choices hcof hfib f.down

def degreeEquiv (a b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    (space hcof hfib a b).obj n ≃ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total (fibers hcof hfib a b)).obj n where
  toFun f := ⟨⟨f.base⟩, SSet.yonedaEquiv f.extension⟩
  invFun f := ⟨f.1.down, SSet.yonedaEquiv.symm f.2⟩
  left_inv f := by
    cases f with
    | mk f e =>
      dsimp only
      congr 1
      exact SSet.yonedaEquiv.symm_apply_apply e
  right_inv := by
    rintro ⟨⟨f⟩, e⟩
    exact congrArg (Sigma.mk (ULift.up f)) (SSet.yonedaEquiv.apply_symm_apply e)

def totalIso (a b : Cᵒᵖ × C) :
    space hcof hfib a b ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.total (fibers hcof hfib a b) :=
  NatIso.ofComponents (fun n => (degreeEquiv hcof hfib a b n).toIso) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    apply congrArg (Sigma.mk (ULift.up f.base))
    exact (SSet.yonedaEquiv_naturality θ.unop f.extension).symm)

def projection (a b : Cᵒᵖ × C) : space hcof hfib a b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels a b) :=
  (totalIso hcof hfib a b).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFamily.projection (fibers hcof hfib a b)

lemma projection_mono_rlp (a b : Cᵒᵖ × C) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp (projection hcof hfib a b) :=
  (MorphismProperty.monomorphisms SSet.{max u v}).rlp.comp_mem _ _
    ((MorphismProperty.monomorphisms SSet.{max u v}).rlp.of_isIso _)
    (DiscreteFamily.projection_mono_rlp _ (fun f => choices_mono_rlp hcof hfib f.down))

lemma projection_localized_isIso (a b : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (projection hcof hfib a b)) :=
  MonoRightLiftingContraction.localized_isIso _ (projection_mono_rlp hcof hfib a b)

lemma kan (a b : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (space hcof hfib a b)) := by
  have hp : SSet.modelCategoryQuillen.J.rlp (projection hcof hfib a b) := by
    intro X Y j hj
    exact projection_mono_rlp hcof hfib a b j
      (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)
  have h := SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ hp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp (labels a b))
  have he : projection hcof hfib a b ≫ terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels a b)) =
      terminal.from (space hcof hfib a b) := terminal.hom_ext _ _
  rwa [he] at h

def composition (a b c : Cᵒᵖ × C) :
    space hcof hfib a b ⊗ space hcof hfib b c ⟶ space hcof hfib a c where
  app _ := ↾fun x => x.1 ≫ x.2
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ((OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map θ.unop)).map_comp
      x.1 x.2).symm

def identity (a : Cᵒᵖ × C) : 𝟙_ SSet.{max u v} ⟶ space hcof hfib a a where
  app n := ↾fun _ => 𝟙 (vertex hcof hfib n a)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro _
    exact ((OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map θ.unop)).map_id _).symm

lemma associativity (a b c d : Cᵒᵖ × C) :
    composition hcof hfib a b c ▷ space hcof hfib c d ≫ composition hcof hfib a c d =
      (α_ (space hcof hfib a b) (space hcof hfib b c) (space hcof hfib c d)).hom ≫
        space hcof hfib a b ◁ composition hcof hfib b c d ≫ composition hcof hfib a b d := by
  ext n x
  exact Category.assoc x.1.1 x.1.2 x.2

lemma left_unit (a b : Cᵒᵖ × C) :
    identity hcof hfib a ▷ space hcof hfib a b ≫ composition hcof hfib a a b =
      (λ_ (space hcof hfib a b)).hom := by
  ext n x
  exact Category.id_comp x.2

lemma right_unit (a b : Cᵒᵖ × C) :
    space hcof hfib a b ◁ identity hcof hfib b ≫ composition hcof hfib a b b =
      (ρ_ (space hcof hfib a b)).hom := by
  ext n x
  exact Category.comp_id x.1

def baseComposition (a b c : Cᵒᵖ × C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels a b) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels b c) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels a c) where
  app _ := ↾fun x => ULift.up (x.1.down ≫ x.2.down)
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def baseIdentity (a : Cᵒᵖ × C) :
    𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (labels a a) where
  app _ := ↾fun _ => ULift.up (𝟙 a)
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

lemma projection_composition (a b c : Cᵒᵖ × C) :
    composition hcof hfib a b c ≫ projection hcof hfib a c =
      (projection hcof hfib a b ⊗ₘ projection hcof hfib b c) ≫ baseComposition a b c := by
  ext n x
  rfl

lemma projection_identity (a : Cᵒᵖ × C) :
    identity hcof hfib a ≫ projection hcof hfib a a = baseIdentity a := by
  ext n x
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace
