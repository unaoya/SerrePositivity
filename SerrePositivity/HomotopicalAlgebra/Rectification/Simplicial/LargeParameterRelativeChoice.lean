module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# 中断した任意モデル源への一般化：LargeParameterRelativeChoice

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All-dimensional relative choices over large parameters。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0444][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0444
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All-dimensional relative choices over large parameters

Small boundary fillers suffice to extend arbitrary prescribed families of
extensions over a large monomorphism. No model structure in the larger
universe is assumed. In particular, homotopies retain the entire specified
subparameter, not just their endpoints.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LargeParameterRelativeChoice
variable {P : SSet.{v}} (hp : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers P)

include hp in
lemma terminal_lifting {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j] :
    HasLiftingProperty j (SSet.stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) where
  sq_hasLift {a _b} _sq := CommSq.HasLift.mk'
    { l := LargeParameterExtension.extend hp j a
      fac_left := LargeParameterExtension.extend_initial hp j a
      fac_right := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }

include hp in
/-- Restriction into the lifted small space lifts every large monomorphism. -/
lemma restriction_lifting {A K U V : SSet.{max w v}} (j : A ⟶ K) [Mono j]
    (l : U ⟶ V) [Mono l] :
    HasLiftingProperty l ((internalHom.map j.op).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{max w v}) j l
  let ph := Functor.PullbackObjObj.ofIsTerminal internalHom j
    (SSet.stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) SSet.stdSimplex.isTerminalObj₀
  have : Mono pp.ι := simplicial_pushoutProduct_mono j l pp
  exact (internalHomAdjunction₂.hasLiftingProperty_iff pp ph).1 (terminal_lifting hp pp.ι)

include hp in
/-- Lift moving boundary families while retaining an already prescribed entire subfamily. -/
lemma family_lifting {A K U V : SSet.{max w v}} (j : A ⟶ K) [Mono j]
    (l : U ⟶ V) [Mono l] (a : K ⊗ U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)
    (c : A ⊗ V ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)
    (hc : j ▷ U ≫ a = A ◁ l ≫ c) :
    ∃ e : K ⊗ V ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P, K ◁ l ≫ e = a ∧ j ▷ V ≫ e = c := by
  have : HasLiftingProperty l ((pre j).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)) := restriction_lifting hp j l
  let sq : CommSq (curry a) l ((pre j).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P))
      (curry c) := ⟨by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left, uncurry_curry]
    exact hc⟩
  refine ⟨uncurry sq.lift, ?_, ?_⟩
  · rw [← uncurry_natural_left, sq.fac_left, uncurry_curry]
  · rw [← uncurry_pre_app, sq.fac_right, uncurry_curry]

variable {A K : SSet.{max w v}} (j : A ⟶ K) [Mono j] (b : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)

include hp in
/-- Extend a family of relative extensions, keeping its entire prescribed domain. -/
lemma extension {U V : SSet.{max w v}} (l : U ⟶ V) [Mono l]
    (a : U ⟶ RelativeChoiceSpace.obj j b) :
    ∃ e : V ⟶ RelativeChoiceSpace.obj j b, l ≫ e = a := by
  have := restriction_lifting hp j l
  have : HasLiftingProperty l (RelativeChoiceSpace.projection j b) := inferInstance
  let sq : CommSq a l (RelativeChoiceSpace.projection j b)
      (SSet.stdSimplex.isTerminalObj₀.from V) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

include hp in
lemma fillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (RelativeChoiceSpace.obj j b) :=
  fun n a => extension hp j b (SSet.boundary.{max w v} n).ι a

def intervalBoundary (s t : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0) ⟶
    RelativeChoiceSpace.obj j b) : (SSet.boundary.{max w v} 1).toSSet ⟶
      RelativeChoiceSpace.obj j b :=
  HomotopyFunctionComplex.BoundaryOne.isColimit.desc (BinaryCofan.mk s t)

def interval (s t : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0) ⟶
    RelativeChoiceSpace.obj j b) : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ⟶
      RelativeChoiceSpace.obj j b :=
  (extension hp j b (SSet.boundary.{max w v} 1).ι (intervalBoundary j b s t)).choose

lemma interval_zero (s t : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0) ⟶
    RelativeChoiceSpace.obj j b) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ interval hp j b s t = s := by
  rw [← SSet.boundary.ι_ι, Category.assoc]
  rw [interval, (extension hp j b (SSet.boundary.{max w v} 1).ι
    (intervalBoundary j b s t)).choose_spec]
  exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.left⟩

lemma interval_one (s t : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 0) ⟶
    RelativeChoiceSpace.obj j b) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ interval hp j b s t = t := by
  rw [← SSet.boundary.ι_ι, Category.assoc]
  rw [interval, (extension hp j b (SSet.boundary.{max w v} 1).ι
    (intervalBoundary j b s t)).choose_spec]
  exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac (BinaryCofan.mk s t) ⟨WalkingPair.right⟩

section ParameterHomotopy
variable {T : SSet.{max w v}} (e₀ e₁ : T ⟶ RelativeChoiceSpace.obj j b)

/-- One interval for an entire family of relative choices, not independently at each point. -/
def parameterHom : T ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ⟶
    RelativeChoiceSpace.obj j b :=
  (extension hp j b (T ◁ (SSet.boundary.{max w v} 1).ι)
    (LargeParameterHomotopy.boundaryMap e₀ e₁)).choose

lemma parameter_face_zero : T ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ parameterHom hp j b e₀ e₁ =
    CategoryTheory.CartesianMonoidalCategory.fst T _ ≫ e₀ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc, parameterHom,
    (extension hp j b (T ◁ (SSet.boundary.{max w v} 1).ι)
      (LargeParameterHomotopy.boundaryMap e₀ e₁)).choose_spec,
    LargeParameterHomotopy.boundaryMap_zero]

lemma parameter_face_one : T ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ parameterHom hp j b e₀ e₁ =
    CategoryTheory.CartesianMonoidalCategory.fst T _ ≫ e₁ := by
  rw [← SSet.boundary.ι_ι, whiskerLeft_comp, Category.assoc, parameterHom,
    (extension hp j b (T ◁ (SSet.boundary.{max w v} 1).ι)
      (LargeParameterHomotopy.boundaryMap e₀ e₁)).choose_spec,
    LargeParameterHomotopy.boundaryMap_one]

def parameterHomotopy : SSet.Homotopy e₀ e₁ where
  h := parameterHom hp j b e₀ e₁
  h₀ := by
    rw [← LargeParameterHomotopy.section_zero T, Category.assoc, parameter_face_zero]
    rfl
  h₁ := by
    rw [← LargeParameterHomotopy.section_one T, Category.assoc, parameter_face_one]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end ParameterHomotopy

variable (e₀ e₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) (h₀ : j ≫ e₀ = b) (h₁ : j ≫ e₁ = b)

/-- An actual homotopy fixing all data on A throughout its entire interval. -/
def fixedHomotopy : RelativeChoiceSpace.FixedBoundaryHomotopy j b e₀ e₁ where
  hom := RelativeChoiceSpace.family j b (interval hp j b
    (RelativeChoiceSpace.ofExtension j b e₀ h₀) (RelativeChoiceSpace.ofExtension j b e₁ h₁))
  at_zero := by
    rw [← RelativeChoiceSpace.family_naturality]
    change RelativeChoiceSpace.family j b (SSet.stdSimplex.δ (1 : Fin 2) ≫ _) = _
    rw [interval_zero, RelativeChoiceSpace.family_ofExtension]
  at_one := by
    rw [← RelativeChoiceSpace.family_naturality]
    change RelativeChoiceSpace.family j b (SSet.stdSimplex.δ (0 : Fin 2) ≫ _) = _
    rw [interval_one, RelativeChoiceSpace.family_ofExtension]
  relative := RelativeChoiceSpace.family_fixed_boundary _ _ _

/-- The same interval, as a simplicial homotopy with its actual endpoints. -/
def homotopy : SSet.Homotopy e₀ e₁ where
  h := (fixedHomotopy hp j b e₀ e₁ h₀ h₁).hom
  h₀ := by
    have h := (fixedHomotopy hp j b e₀ e₁ h₀ h₁).at_zero
    change K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ _ = _ at h
    rw [← LargeParameterHomotopy.section_zero K, Category.assoc, h]
    rfl
  h₁ := by
    have h := (fixedHomotopy hp j b e₀ e₁ h₀ h₁).at_one
    change K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ _ = _ at h
    rw [← LargeParameterHomotopy.section_one K, Category.assoc, h]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

lemma homotopy_relative : j ▷ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ≫
    (homotopy hp j b e₀ e₁ h₀ h₁).h =
      A ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ A).hom ≫ b := (fixedHomotopy hp j b e₀ e₁ h₀ h₁).relative

end SerrePositivity.SimplicialModel.LargeParameterRelativeChoice
