module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.FixedBoundaryExtensions

public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# 中断した任意モデル源への一般化：RecursiveChoiceExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Recursive extension of prescribed coherent families。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0518][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0518
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Recursive extension of prescribed coherent families

The actual skeletal filtration of a monomorphism supplies the stages.
Each stage extends its predecessor, and their colimit is one simplicial map.
Thus every earlier choice and all face and degeneracy identities are retained.
The input is a partial simplicial map, not an unrelated collection of faces.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.RecursiveChoiceExtension

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
  (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
  (hp : trivialFibrations SSet.{v} p)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j]
  (a : A ⟶ RelativeChoiceSpace.obj i b)

abbrev filtration := (SSet.relativeCellComplexOfMono j).F

def next (n : ℕ) (e : (filtration j).obj n ⟶ RelativeChoiceSpace.obj i b) :
    {e' : (filtration j).obj (n + 1) ⟶ RelativeChoiceSpace.obj i b //
      (filtration j).map (homOfLE (Nat.le_succ n)) ≫ e' = e} := by
  have : Mono ((filtration j).map (homOfLE (Nat.le_succ n))) := by
    change Mono (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono j).monotone (Nat.le_succ n)))
    infer_instance
  exact ⟨_, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib i b p hp
    ((filtration j).map (homOfLE (Nat.le_succ n))) e).choose_spec⟩

abbrev initial : (filtration j).obj 0 ⟶ RelativeChoiceSpace.obj i b :=
  (SSet.relativeCellComplexOfMono j).isoBot.hom ≫ a

def stage (n : ℕ) : (filtration j).obj n ⟶ RelativeChoiceSpace.obj i b :=
  SequentialExtension.stage (filtration j) _ (next hcof hfib i b p hp j) (initial i b j a) n

@[reassoc]
lemma stage_succ (n : ℕ) :
    (filtration j).map (homOfLE (Nat.le_succ n)) ≫ stage hcof hfib i b p hp j a (n + 1) =
      stage hcof hfib i b p hp j a n :=
  SequentialExtension.stage_succ _ _ _ _ n

@[reassoc]
lemma stage_map {n m : ℕ} (f : n ⟶ m) :
    (filtration j).map f ≫ stage hcof hfib i b p hp j a m =
      stage hcof hfib i b p hp j a n :=
  SequentialExtension.stage_map _ _ _ _ f

def extend : K ⟶ RelativeChoiceSpace.obj i b :=
  SequentialExtension.descend (filtration j) _ (next hcof hfib i b p hp j) (initial i b j a)
    (Cocone.mk K (SSet.relativeCellComplexOfMono j).incl)
    (SSet.relativeCellComplexOfMono j).isColimit

@[reassoc]
lemma extend_stage (n : ℕ) :
    (SSet.relativeCellComplexOfMono j).incl.app n ≫ extend hcof hfib i b p hp j a =
      stage hcof hfib i b p hp j a n :=
  SequentialExtension.descend_stage (filtration j) _ (next hcof hfib i b p hp j)
    (initial i b j a) (Cocone.mk K (SSet.relativeCellComplexOfMono j).incl)
    (SSet.relativeCellComplexOfMono j).isColimit n

@[reassoc]
lemma extend_initial : j ≫ extend hcof hfib i b p hp j a = a := by
  calc
    j ≫ extend hcof hfib i b p hp j a =
        ((SSet.relativeCellComplexOfMono j).isoBot.inv ≫
          (SSet.relativeCellComplexOfMono j).incl.app 0) ≫
            extend hcof hfib i b p hp j a :=
      congrArg (fun q => q ≫ extend hcof hfib i b p hp j a)
        (SSet.relativeCellComplexOfMono j).fac.symm
    _ = a := by
      rw [Category.assoc, extend_stage]
      change (SSet.relativeCellComplexOfMono j).isoBot.inv ≫
        ((SSet.relativeCellComplexOfMono j).isoBot.hom ≫ a) = a
      exact Iso.inv_hom_id_assoc (SSet.relativeCellComplexOfMono j).isoBot a

/-- Retain any specified simplex of the original partial family. -/
@[reassoc]
lemma extend_prescribed {n : ℕ} (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ A) :
    (s ≫ j) ≫ extend hcof hfib i b p hp j a = s ≫ a := by
  rw [Category.assoc, extend_initial]

/-- An n-simplex already lies in the stage containing all simplices of dimension ≤ n. -/
def simplexAtStage {n : ℕ} (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ K) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ (filtration j).obj (n + 1) :=
  SSet.Subcomplex.lift s (by
    rw [SSet.Subcomplex.range_eq_ofSimplex]
    exact (K.ofSimplex_le_skeleton _ (Nat.lt_succ_self n)).trans
      (SSet.skeleton_le_skeletonOfMono j (n + 1)))

omit [ModelCategory SSet.{v}] in
@[reassoc]
lemma simplexAtStage_inclusion {n : ℕ}
    (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ K) :
    simplexAtStage j s ≫ (SSet.relativeCellComplexOfMono j).incl.app (n + 1) = s := rfl

/-- The colimit map uses the actual finite-stage choice on every finite simplex. -/
lemma extend_simplex {n : ℕ} (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ K) :
    s ≫ extend hcof hfib i b p hp j a =
      simplexAtStage j s ≫ stage hcof hfib i b p hp j a (n + 1) := by
  calc
    s ≫ extend hcof hfib i b p hp j a =
        (simplexAtStage j s ≫ (SSet.relativeCellComplexOfMono j).incl.app (n + 1)) ≫
          extend hcof hfib i b p hp j a := rfl
    _ = _ := by rw [Category.assoc, extend_stage]

/-- All simplicial operators commute with the same globally chosen extension. -/
lemma simplex_naturality {n m : ℕ}
    (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ K)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ (s ≫ extend hcof hfib i b p hp j a) =
      (SSet.stdSimplex.map θ ≫ s) ≫ extend hcof hfib i b p hp j a :=
  (Category.assoc _ _ _).symm

@[reassoc]
lemma family_prescribed :
    T ◁ j ≫ RelativeChoiceSpace.family i b (extend hcof hfib i b p hp j a) =
      RelativeChoiceSpace.family i b a := by
  rw [← RelativeChoiceSpace.family_naturality, extend_initial]

lemma fixed_boundary :
    i ▷ K ≫ RelativeChoiceSpace.family i b (extend hcof hfib i b p hp j a) =
      V ◁ (SSet.stdSimplex.isTerminalObj₀.from K ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ V).hom ≫ b :=
  RelativeChoiceSpace.family_fixed_boundary i b _

end SerrePositivity.SimplicialModel.RecursiveChoiceExtension
