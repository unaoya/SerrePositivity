module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.FixedBoundaryExtensions

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SkeletalCellGluing
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace

/-!
# 中断した任意モデル源への一般化：RelativeChoiceCells

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Cell-filling rules supplied by the actual relative choice space。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0536][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0536
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Cell-filling rules supplied by the actual relative choice space

No system of higher fillers is assumed: the relative choice-space trivial
fibration supplies a filler of every actual attaching boundary. The skeletal
assembly can retain additionally prescribed simplices with boundary in A.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.RelativeChoiceCells

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
  (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
  (hp : trivialFibrations SSet.{v} p)
  {A K : SSet.{v}} (j : A ⟶ K) [Mono j]

def rule : SkeletalCellGluing.Rule (Q := RelativeChoiceSpace.obj i b) j := by
  intro n a c
  let ex := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib i b p hp
    (SSet.boundary.{v} n).ι (SkeletalCellGluing.boundary j c ≫ a)
  exact ⟨ex.choose, ex.choose_spec⟩

variable (a₀ : A ⟶ RelativeChoiceSpace.obj i b)
  (prescribed : ∀ n, SSet.relativeCellComplexOfMono.Cell j n →
    Option (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ RelativeChoiceSpace.obj i b))

def assemble : K ⟶ RelativeChoiceSpace.obj i b :=
  SkeletalCellGluing.assemble j
    (SkeletalCellGluing.override j (rule hcof hfib i b p hp j) prescribed) a₀

@[reassoc]
lemma assemble_initial : j ≫ assemble hcof hfib i b p hp j a₀ prescribed = a₀ :=
  SkeletalCellGluing.assemble_initial j _ a₀

lemma assemble_prescribed {n : ℕ} (c : SSet.relativeCellComplexOfMono.Cell j n)
    (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ RelativeChoiceSpace.obj i b)
    (hs : prescribed n c = some s) (q : (SSet.boundary.{v} n).toSSet ⟶ A)
    (hq : q ≫ j = (SSet.boundary.{v} n).ι ≫ c.map)
    (ha : q ≫ a₀ = (SSet.boundary.{v} n).ι ≫ s) :
    c.map ≫ assemble hcof hfib i b p hp j a₀ prescribed = s :=
  SkeletalCellGluing.assemble_prescribed j (rule hcof hfib i b p hp j) a₀
    prescribed c s hs q hq ha

@[reassoc]
lemma family_initial :
    T ◁ j ≫ RelativeChoiceSpace.family i b (assemble hcof hfib i b p hp j a₀ prescribed) =
      RelativeChoiceSpace.family i b a₀ := by
  rw [← RelativeChoiceSpace.family_naturality, assemble_initial]

lemma fixed_boundary :
    i ▷ K ≫ RelativeChoiceSpace.family i b (assemble hcof hfib i b p hp j a₀ prescribed) =
      V ◁ (SSet.stdSimplex.isTerminalObj₀.from K ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ V).hom ≫ b :=
  RelativeChoiceSpace.family_fixed_boundary i b _

end SerrePositivity.SimplicialModel.RelativeChoiceCells
