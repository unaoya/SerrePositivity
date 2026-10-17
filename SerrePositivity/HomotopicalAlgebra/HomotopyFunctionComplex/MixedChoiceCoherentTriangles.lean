module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBoundaryExtension
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals

/-!
# 中断した任意モデル源への一般化：MixedChoiceCoherentTriangles

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole coherent mixed triangles sharing the same whole diagonal system。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0115][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0115
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole coherent mixed triangles sharing the same whole diagonal system
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.NerveSimplexEndpoint
open SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals

namespace SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentTriangles
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

def faceEdge (left : Bool) : Fin 3 → Edge :=
  if left then ![.BD, .AD, .AB] else ![.CD, .AD, .AC]

abbrev faces (left : Bool) (k : Fin 3) := interval hcof hfib Y W g (faceEdge left k)

include hcof hfib in
lemma faces_compatible (left : Bool) :
    NerveBoundaryExtension.Compatible (values hcof Y W g) (faces hcof hfib Y W g left) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · cases left
    · exact (interval_one hcof hfib Y W g .CD).trans
        (interval_one hcof hfib Y W g .AD).symm
    · exact (interval_one hcof hfib Y W g .BD).trans
        (interval_one hcof hfib Y W g .AD).symm
  · cases left
    · exact (interval_zero hcof hfib Y W g .CD).trans
        (interval_one hcof hfib Y W g .AC).symm
    · exact (interval_zero hcof hfib Y W g .BD).trans
        (interval_one hcof hfib Y W g .AB).symm
  · cases left
    · exact (interval_zero hcof hfib Y W g .AD).trans
        (interval_zero hcof hfib Y W g .AC).symm
    · exact (interval_zero hcof hfib Y W g .AD).trans
        (interval_zero hcof hfib Y W g .AB).symm

abbrev oldTriangle (left : Bool) (t : MixedChoiceFunctor.Context Y W) :=
  CoherentLiftMixedComparison.triangle hcof hfib t.1.unop.left.inner Y.inner W t.2.right
    t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) left

lemma oldTriangle_face (left : Bool) (t : MixedChoiceFunctor.Context Y W) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ oldTriangle hcof hfib Y W g left t =
      oldEdge hcof hfib Y W g (faceEdge left k) t := by
  cases left <;> fin_cases k <;>
    exact CoherentLiftMixedComparison.triangle_face hcof hfib
      t.1.unop.left.inner Y.inner W t.2.right t.1.unop.hom.map g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) _ _

lemma faces_component (left : Bool) (k : Fin 3)
    (s : Reedy.Lower (NerveCoherentFamily.reedy (MixedChoiceFunctor.Context Y W)) 1) :
    (faces hcof hfib Y W g left k).app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.name (SSet.stdSimplex.δ k ≫
        oldTriangle hcof hfib Y W g left (endpoint s.obj)) := by
  apply (interval_component hcof hfib Y W g (faceEdge left k) s).trans
  exact congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name e)
    (oldTriangle_face hcof hfib Y W g left (endpoint s.obj) k).symm

/-- Retain the original whole triangle, with all three already coherent edge systems fixed. -/
def triangle (left : Bool) : NerveParameterExtension.System (values hcof Y W g)
    (SSet.stdSimplex.obj (SimplexCategory.mk 2)) :=
  NerveBoundaryExtension.extend (values hcof Y W g) (faces hcof hfib Y W g left)
    (faces_compatible hcof hfib Y W g left) (oldTriangle hcof hfib Y W g left)
    (faces_component hcof hfib Y W g left) hcof hfib (projection_trivialFibration hcof hfib Y W g)

lemma triangle_evaluate (left : Bool) (t : MixedChoiceFunctor.Context Y W) :
    NerveParameterExtension.evaluate (values hcof Y W g) (triangle hcof hfib Y W g left) t =
      oldTriangle hcof hfib Y W g left t :=
  NerveBoundaryExtension.extend_evaluate _ _ _ _ _ _ _ _ t

lemma triangle_face (left : Bool) (k : Fin 3) : triangle hcof hfib Y W g left ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ k)) = faces hcof hfib Y W g left k :=
  NerveBoundaryExtension.extend_face _ _ _ _ _ _ _ _ k

lemma shared_diagonal : triangle hcof hfib Y W g true ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 3))) =
    triangle hcof hfib Y W g false ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 3))) :=
  (triangle_face hcof hfib Y W g true 1).trans (triangle_face hcof hfib Y W g false 1).symm

end SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentTriangles
