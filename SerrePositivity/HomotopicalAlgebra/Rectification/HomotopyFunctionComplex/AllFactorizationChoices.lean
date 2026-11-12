module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterRelativeChoice
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterSquare

/-!
# 中断した任意モデル源への一般化：AllFactorizationChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One space of all global comparison systems with the prescribed factorization points。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0047][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0047
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One space of all global comparison systems with the prescribed factorization points

All choices are actual maps on the entire nerve, with the same original
factorization points. Every compatible boundary of choices extends at once,
and comparisons retain those points throughout the entire parameter.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationChoices
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V)

include hcof hfib in
lemma valueFillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (AllFactorizationComparison.choiceSpace f g) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.relativeFillers hcof hfib (vertexInclusion X Y f) (postBoundary X Y V f g)
    (ResolutionLiftSpace.projection X V (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ g.base))

abbrev obj : SSet.{max u v} :=
  RelativeChoiceSpace.obj (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g)

/-- The existing globally selected family is a point of this one space of all choices. -/
abbrev chosenPoint : SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) ⟶ obj hcof f g :=
  RelativeChoiceSpace.ofExtension (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g)
    (AllFactorizationComparison.comparison hcof hfib f g)
    (AllFactorizationComparison.comparison_vertices hcof hfib f g)

/-- Evaluation retains the entire nerve parameter as well as the entire choice parameter. -/
abbrev universalFamily : nerve (ArrowFactorization g) ⊗ obj hcof f g ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g) :=
  RelativeChoiceSpace.family (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g) (𝟙 _)

lemma universal_fixed_vertices :
    NerveVertices.inclusion (ArrowFactorization g) ▷ obj hcof f g ≫
        universalFamily hcof f g =
      NerveVertices.vertices (ArrowFactorization g) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          AllFactorizationComparison.vertexData hcof f g :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

include hcof hfib in
lemma extension {A K : SSet.{max u v}} (j : A ⟶ K) [Mono j] (b : A ⟶ obj hcof f g) :
    ∃ e : K ⟶ obj hcof f g, j ≫ e = b :=
  LargeParameterRelativeChoice.extension (valueFillers hcof hfib f g)
    (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g) j b

include hcof hfib in
lemma fillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (obj hcof f g) :=
  fun n b => extension hcof hfib f g (SSet.boundary.{max u v} n).ι b

include hcof hfib in
/-- Existing systems and moving factorization-point data are both retained as actual maps. -/
lemma extendMovingVertices {A K : SSet.{max u v}} (j : A ⟶ K) [Mono j]
    (a : nerve (ArrowFactorization g) ⊗ A ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g))
    (c : NerveVertices.vertices (ArrowFactorization g) ⊗ K ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g))
    (hc : NerveVertices.inclusion (ArrowFactorization g) ▷ A ≫ a =
      NerveVertices.vertices (ArrowFactorization g) ◁ j ≫ c) :
    ∃ e : nerve (ArrowFactorization g) ⊗ K ⟶
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g),
      nerve (ArrowFactorization g) ◁ j ≫ e = a ∧
        NerveVertices.inclusion (ArrowFactorization g) ▷ K ≫ e = c :=
  LargeParameterRelativeChoice.family_lifting (valueFillers hcof hfib f g)
    (NerveVertices.inclusion (ArrowFactorization g)) j a c hc

abbrev collapse : obj hcof f g ⟶ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0) :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- One contraction of the entire space of coherent systems, preserving their vertex data. -/
def contraction : SSet.Homotopy (collapse hcof f g ≫ chosenPoint hcof hfib f g)
    (𝟙 (obj hcof f g)) :=
  LargeParameterRelativeChoice.parameterHomotopy (valueFillers hcof hfib f g)
    (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g)
    (collapse hcof f g ≫ chosenPoint hcof hfib f g) (𝟙 _)

/-- The evaluated contraction is a single map on all nerve and choice parameters. -/
abbrev universalContraction : nerve (ArrowFactorization g) ⊗
    (obj hcof f g ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g) :=
  RelativeChoiceSpace.family (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g) (contraction hcof hfib f g).h

lemma universalContraction_zero : nerve (ArrowFactorization g) ◁ SSet.ι₀ ≫
    universalContraction hcof hfib f g =
      nerve (ArrowFactorization g) ◁ collapse hcof f g ≫
        nerve (ArrowFactorization g) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
          (ρ_ _).hom ≫ AllFactorizationComparison.comparison hcof hfib f g := by
  rw [universalContraction, ← RelativeChoiceSpace.family_naturality,
    (contraction hcof hfib f g).h₀, RelativeChoiceSpace.family_naturality,
    RelativeChoiceSpace.family_ofExtension]

lemma universalContraction_one : nerve (ArrowFactorization g) ◁ SSet.ι₁ ≫
    universalContraction hcof hfib f g = universalFamily hcof f g := by
  rw [universalContraction, ← RelativeChoiceSpace.family_naturality,
    (contraction hcof hfib f g).h₁]

lemma universalContraction_fixed_vertices :
    NerveVertices.inclusion (ArrowFactorization g) ▷
        (obj hcof f g ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
        universalContraction hcof hfib f g =
      NerveVertices.vertices (ArrowFactorization g) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          AllFactorizationComparison.vertexData hcof f g :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

variable (s : nerve (ArrowFactorization g) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (AllFactorizationComparison.choiceSpace f g))
  (hs : NerveVertices.inclusion (ArrowFactorization g) ≫ s =
    AllFactorizationComparison.vertexData hcof f g)

/-- One global comparison fixes all originally specified factorization points throughout. -/
abbrev homotopy : SSet.Homotopy (AllFactorizationComparison.comparison hcof hfib f g) s :=
  LargeParameterRelativeChoice.homotopy (valueFillers hcof hfib f g)
    (NerveVertices.inclusion (ArrowFactorization g))
    (AllFactorizationComparison.vertexData hcof f g)
    (AllFactorizationComparison.comparison hcof hfib f g) s
    (AllFactorizationComparison.comparison_vertices hcof hfib f g) hs

lemma homotopy_fixed_vertices :
    NerveVertices.inclusion (ArrowFactorization g) ▷
        SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫ (homotopy hcof hfib f g s hs).h =
      NerveVertices.vertices (ArrowFactorization g) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          AllFactorizationComparison.vertexData hcof f g :=
  LargeParameterRelativeChoice.homotopy_relative _ _ _ _ _ _ _

/-- The same comparison acts on all anchored chains, retaining all simplicial operators. -/
def chainHomotopy : SSet.Homotopy (AllFactorizationComparison.chainComparison hcof hfib f g)
    ((AnchoredChain.nerveIso g).inv ≫ s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport (AnchoredChain.nerveIso g).inv (𝟙 _)
      (homotopy hcof hfib f g s hs))
    (by simp only [Category.comp_id]) (by simp only [Category.comp_id])

/-- Finite values of the comparison of entire systems lie in the original Hom universe. -/
def simplex {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      AllFactorizationComparison.choiceSpace f g :=
  SSet.yonedaEquiv.symm
    (((chainHomotopy hcof hfib f g s hs).h.app (Opposite.op (SimplexCategory.mk n)) (c, t)).down)

lemma simplex_naturality {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof hfib f g s hs c t =
      simplex hcof hfib f g s hs (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).map θ.op t) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_naturality]
  simp only [simplex, Equiv.apply_symm_apply]
  exact (congrArg ULift.down (congrArg (fun q => q (c, t))
    ((chainHomotopy hcof hfib f g s hs).h.naturality θ.op))).symm

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationChoices
