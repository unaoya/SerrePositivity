module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarFirstAction
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift

/-!
# 中断した任意モデル源への一般化：ResolutionBarEvaluation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Evaluation of the actual resolution bar in the small mixed reference Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0290][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0290
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Evaluation of the actual resolution bar in the small mixed reference Hom

All comma chains and their element labels are retained. First-endpoint
coherent lift families give a simplicial map into the lifted small output.
No weak equivalence of this evaluation or of the bar unit is asserted here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarEvaluation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev raw : RightResolutionMapping.Index C ⥤ SSet.{v} := MixedBiresolutionComparison.functor
abbrev bar : SSet.{max u v} :=
  (BarConstruction.relative (RightResolutionMapping.projection (C := C)) raw).obj
    ((RightResolutionMapping.projection (C := C)).obj R)

/-- Forget only the element label; keep the same comma arrow and all actual comparison maps. -/
def forgetElements (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (BarConstruction.elementProjection
      (RightResolutionMapping.projection (C := C)) raw n)
      ((RightResolutionMapping.projection (C := C)).obj R) ⥤ ResolutionBarCenters.Comma R where
  obj e := CostructuredArrow.mk (Y := e.left.obj) e.hom
  map k := CostructuredArrow.homMk k.left.hom (CostructuredArrow.w k)

abbrev chain (n : SimplexCategoryᵒᵖ) (c : (bar R).obj n) := c ⋙ forgetElements R n

lemma chain_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (c : (bar R).obj n) :
    chain R m ((bar R).map θ c) = (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ chain R n c := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

abbrev inputSimplex (n : SimplexCategoryᵒᵖ) (c : (bar R).obj n) :
    SSet.stdSimplex.{v}.obj n.unop ⟶ ResolutionBarFirstAction.input R ((chain R n c).obj 0) :=
  SSet.yonedaEquiv.symm (c.obj 0).left.val

variable (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

abbrev simplex (n : SimplexCategoryᵒᵖ) (c : (bar R).obj n) :
    SSet.stdSimplex.{v}.obj n.unop ⟶ BarOutput.output R :=
  ResolutionBarFirstAction.action R a b (chain R n c) (inputSimplex R n c)

lemma input_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (c : (bar R).obj n) :
    inputSimplex R m ((bar R).map θ c) =
      (SSet.stdSimplex.map θ.unop ≫ inputSimplex R n c) ≫ raw.map
        ((chain R n c).map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left := by
  rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  have h := (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.map_val
  change ((raw.obj (c.obj (θ.unop.toOrderHom 0)).left.obj).map θ
    (c.obj (θ.unop.toOrderHom 0)).left.val) =
      (raw.map (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.hom).app m
        ((raw.obj (c.obj 0).left.obj).map θ (c.obj 0).left.val)
  rw [← h]
  exact (congrArg (fun k => k (c.obj 0).left.val)
    ((raw.map (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.hom).naturality θ)).symm

lemma simplex_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (c : (bar R).obj n) :
    SSet.stdSimplex.map θ.unop ≫ simplex R a b n c =
      simplex R a b m ((bar R).map θ c) := by
  unfold simplex
  rw [ResolutionBarFirstAction.operator]
  simp only [input_operator]
  congr 1

/-- A genuine map from the whole large bar to the lift of the same small reference output. -/
def evaluation : bar R ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (BarOutput.output R) where
  app n := ↾fun c => ULift.up (SSet.yonedaEquiv (simplex R a b n c))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    change SSet.yonedaEquiv (simplex R a b m ((bar R).map θ c)) =
      (BarOutput.output R).map θ (SSet.yonedaEquiv (simplex R a b n c))
    exact (congrArg SSet.yonedaEquiv (simplex_operator R a b θ c)).symm.trans
      (SSet.yonedaEquiv_naturality θ.unop (simplex R a b n c)).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarEvaluation
