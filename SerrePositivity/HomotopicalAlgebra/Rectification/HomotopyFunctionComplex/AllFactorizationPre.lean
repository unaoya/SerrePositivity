module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationPost
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftMixedComparison

/-!
# 中断した任意モデル源への一般化：AllFactorizationPre

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Source precomposition of the global factorization comparison。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0056][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0056
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Source precomposition of the global factorization comparison

The actual frame map acts on the old global family. The new-source family
is restricted along the strict precomposition of lift tuples. Both have
the same fixed boundary in the existing mixed relative choice space.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationPre
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X Y V : ResolutionObject C} (a : X' ⟶ X) (f : X.base ⟶ Y.base) (g : Y ⟶ V)
  (φ : ResolutionLiftPrecomposition.FrameMap a)

abbrev choiceSpace : SSet.{v} := CoherentLiftMixedComparison.space X' X Y V a f g φ

abbrev direct : AnchoredChain.simplicial g ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (choiceSpace a f g φ) :=
  AllFactorizationComparison.chainComparison hcof hfib (a.base ≫ f) g ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapBD hcof X' X Y V a f g φ)

abbrev transported : AnchoredChain.simplicial g ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (choiceSpace a f g φ) :=
  AllFactorizationComparison.chainComparison hcof hfib f g ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapAC X' X Y V a f g φ)

include hcof hfib in
lemma fillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (choiceSpace a f g φ) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.relativeFillers hcof hfib (vertexInclusion X Y f)
    (CoherentLiftMixedComparison.boundary X' X Y V a f g φ)
    (ResolutionLiftSpace.projection X' V (a.base ≫ f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X' V (a.base ≫ f ≫ g.base))

def homotopy :
    SSet.Homotopy (direct hcof hfib a f g φ) (transported hcof hfib a f g φ) :=
  LargeParameterHomotopy.homotopy (fillers hcof hfib a f g φ)
    (direct hcof hfib a f g φ) (transported hcof hfib a f g φ)

/-- Every finite value of the one global homotopy lies in the original universe. -/
def simplex {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ choiceSpace a f g φ :=
  SSet.yonedaEquiv.symm
    ((((homotopy hcof hfib a f g φ).h).app (Opposite.op (SimplexCategory.mk n)) (c, t)).down)

/-- The chain and interval parameters obey every face and degeneracy simultaneously. -/
lemma simplex_naturality {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof hfib a f g φ c t =
      simplex hcof hfib a f g φ (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).map θ.op t) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_naturality]
  simp only [simplex, Equiv.apply_symm_apply]
  exact (congrArg ULift.down (congrArg (fun q => q (c, t))
    ((homotopy hcof hfib a f g φ).h.naturality θ.op))).symm

lemma simplex_fixed_boundary {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f)
        (CoherentLiftMixedComparison.boundary X' X Y V a f g φ)
        (simplex hcof hfib a f g φ c t) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          CoherentLiftMixedComparison.boundary X' X Y V a f g φ :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationPre
