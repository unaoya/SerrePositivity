module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChainTransport
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftTensor

/-!
# 中断した任意モデル源への一般化：AnchoredChainFiniteTest

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole finite test parameters of the actual large factorization-chain space。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0339][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0339
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole finite test parameters of the actual large factorization-chain space
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift

/-- The same lifted small set with an already absorbed universe level relabelled. -/
def stableIso (P : SSet.{v}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} P ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} P :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro n m θ; ext x; rfl)

lemma stableIso_naturality {P Q : SSet.{v}} (f : P ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} f ≫ (stableIso Q).hom = (stableIso P).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} f := by
  ext n x
  rfl

end SerrePositivity.SimplicialModel.UniverseLift

namespace SerrePositivity.SimplicialModel.AnchoredChainFiniteTest
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

abbrev smallParameter (m r : ℕ) : SSet.{v} :=
  SSet.stdSimplex.obj (SimplexCategory.mk m) ⊗ SSet.stdSimplex.obj (SimplexCategory.mk r)
abbrev parameter (r : ℕ) := AnchoredChain.simplicial g ⊗
  SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk r)

abbrev simplex {m : ℕ} (c : AnchoredChain g m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m)) ⟶
      AnchoredChain.simplicial g :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso m).hom ≫ (SSet.yonedaEquiv (X := AnchoredChain.simplicial g)).symm c

lemma simplex_reindex {m n : ℕ} (c : AnchoredChain g m)
    (ψ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.map ψ) ≫ simplex g c =
      simplex g (c.reindex ψ.toOrderHom) := by
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.map ψ) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso m).hom ≫ (SSet.yonedaEquiv (X := AnchoredChain.simplicial g)).symm c) = _
  rw [← Category.assoc]
  have hu : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.{v}.map ψ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso m).hom = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso n).hom ≫ SSet.stdSimplex.map ψ := rfl
  rw [hu, Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  rfl

/-- Keep the entire supplementary simplex, not just its vertices or sampled points. -/
def test {m : ℕ} (c : AnchoredChain g m) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (smallParameter.{v} m r) ⟶ parameter g r :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorIso (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m))
    (SSet.stdSimplex.obj (SimplexCategory.mk r))).hom ≫
    (simplex g c ▷ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (SSet.stdSimplex.obj (SimplexCategory.mk r))) ≫
    (AnchoredChain.simplicial g ◁ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso r).hom)

lemma test_operator {m r s : ℕ} (c : AnchoredChain g m)
    (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk s) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.map θ) ≫
      test g c s = test g c r ≫ AnchoredChain.simplicial g ◁ SSet.stdSimplex.map θ := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  rfl

lemma test_reindex {m n : ℕ} (c : AnchoredChain g m)
    (ψ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk r)) ≫
      test g c r = test g (c.reindex ψ.toOrderHom) r := by
  apply NatTrans.ext
  funext d
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  apply Prod.ext
  · exact congrArg (fun z => z.app d (ULift.up x.down.1)) (simplex_reindex g c ψ)
  · rfl

end SerrePositivity.SimplicialModel.AnchoredChainFiniteTest
