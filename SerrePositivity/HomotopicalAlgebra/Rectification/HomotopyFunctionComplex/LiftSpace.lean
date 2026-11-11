module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# 中断した任意モデル源への一般化：LiftSpace

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Spaces of lifts of augmented cosimplicial frames。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0104][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0104
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Spaces of lifts of augmented cosimplicial frames

The fiber is an actual simplicial set. For a trivial fibration its map to
Delta[0] is a trivial fibration: all finite-dimensional compatibility data
can therefore be extended. Source functorial factorization is not required.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.LiftSpace
variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C) {X : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)

/-- A genuine constant simplex of the actual Hom, from an augmentation. -/
def point {B : C} (f : X ⟶ B) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B where
  app n := ↾fun _ => a.app n.unop ≫ f
  naturality {n m} g := by
    ext s
    change a.app m.unop ≫ f = A.map g.unop ≫ (a.app n.unop ≫ f)
    have h := a.naturality g.unop
    change A.map g.unop ≫ a.app n.unop = a.app m.unop ≫ 𝟙 X at h
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ f) (h.trans (Category.comp_id _)))).symm

@[reassoc]
lemma point_postcomp {E B : C} (e : X ⟶ E) (p : E ⟶ B) :
    point A a e ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p = point A a (e ≫ p) := by
  ext n s
  exact Category.assoc _ _ _

/-- The actual fiber of Hom(A,p) over the constant simplex a followed by f. -/
abbrev obj {E B : C} (p : E ⟶ B) (f : X ⟶ B) : SSet.{v} :=
  pullback ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) (point A a f)

abbrev inclusion {E B : C} (p : E ⟶ B) (f : X ⟶ B) :
    obj A a p f ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj E :=
  pullback.fst _ _

abbrev projection {E B : C} (p : E ⟶ B) (f : X ⟶ B) :
    obj A a p f ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) :=
  pullback.snd _ _

@[reassoc]
lemma over {E B : C} (p : E ⟶ B) (f : X ⟶ B) :
    inclusion A a p f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p =
      projection A a p f ≫ point A a f := pullback.condition

/-- Any strict lift gives an actual point of the lift space. -/
def ofLift {E B : C} (p : E ⟶ B) (f : X ⟶ B) (e : X ⟶ E) (he : e ≫ p = f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj A a p f :=
  pullback.lift (point A a e) (𝟙 _) (by rw [point_postcomp, he, Category.id_comp])

@[reassoc (attr := simp)]
lemma ofLift_inclusion {E B : C} (p : E ⟶ B) (f : X ⟶ B) (e : X ⟶ E)
    (he : e ≫ p = f) :
    ofLift A a p f e he ≫ inclusion A a p f = point A a e := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma ofLift_projection {E B : C} (p : E ⟶ B) (f : X ⟶ B) (e : X ⟶ E)
    (he : e ≫ p = f) :
    ofLift A a p f e he ≫ projection A a p f = 𝟙 _ := pullback.lift_snd _ _ _

variable [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))

include hcof hA in
lemma projection_trivialFibration {E B : C} (p : E ⟶ B)
    [Fibration p] [WeakEquivalence p] (f : X ⟶ B) :
    trivialFibrations SSet.{v} (projection A a p f) :=
  (trivialFibrations SSet.{v}).of_isPullback
    (IsPullback.of_hasPullback ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) (point A a f))
    (cosimplicialHom_trivialFibration hcof A hA p)

include hcof hA in
/-- All boundary data, and more generally every monomorphism, can be filled. -/
lemma extension {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (f : X ⟶ B) {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (g : K ⟶ obj A a p f) :
    ∃ e : L ⟶ obj A a p f, i ≫ e = g := by
  have hi : cofibrations SSet.{v} i := by rw [hcof]; infer_instance
  have hp := projection_trivialFibration A a hcof hA p f
  have : HasLiftingProperty i (projection A a p f) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ hi hp
  let sq : CommSq g i (projection A a p f)
      (SSet.stdSimplex.isTerminalObj₀.from L) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Chosen fillers in every dimension, preserving all prescribed boundary data. -/
def boundaryFiller {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (f : X ⟶ B) (n : ℕ) (g : (SSet.boundary.{v} n).toSSet ⟶ obj A a p f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ obj A a p f :=
  (extension A a hcof hA p f (SSet.boundary n).ι g).choose

@[reassoc (attr := simp)]
lemma boundaryFiller_fac {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (f : X ⟶ B) (n : ℕ) (g : (SSet.boundary.{v} n).toSSet ⟶ obj A a p f) :
    (SSet.boundary n).ι ≫ boundaryFiller A a hcof hA p f n g = g :=
  (extension A a hcof hA p f (SSet.boundary n).ι g).choose_spec

include hcof hA in
lemma isFibrant {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (f : X ⟶ B) : IsFibrant (obj A a p f) :=
  (isFibrant_iff_of_isTerminal (projection A a p f) SSet.stdSimplex.isTerminalObj₀).mpr
    ⟨(projection_trivialFibration A a hcof hA p f).1⟩

include hcof hA in
lemma kanComplex (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (f : X ⟶ B) : SSet.KanComplex (obj A a p f) := by
  have : IsFibrant (obj A a p f) := isFibrant A a hcof hA p f
  apply (SSet.modelCategoryQuillen.fibration_iff (terminal.from (obj A a p f))).mpr
  rw [← hfib]
  exact mem_fibrations _

/-- Contractibility is witnessed by the actual projection to the point. -/
def localizationIso (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {H : Type*} [Category* H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})]
    {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p] (f : X ⟶ B) :
    L.obj (obj A a p f) ≅ L.obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) := by
  have : IsIso (L.map (projection A a p f)) :=
    Localization.inverts L (weakEquivalences SSet.{v}) _
      (projection_trivialFibration A a hcof hA p f).2
  exact asIso (L.map (projection A a p f))

end SerrePositivity.HomotopyFunctionComplex.LiftSpace
