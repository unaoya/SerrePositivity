module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveLargeParameter
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixedContext

/-!
# 中断した任意モデル源への一般化：AllFactorizationCoherentSquare

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One external coherent square retaining the entire old all-factorization parameter。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0048][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0048
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One external coherent square retaining the entire old all-factorization parameter

The two old global triangles are glued along their actual common diagonal
before making any external coherent choices. This retains both whole
triangles and their four global homotopy edges at each original context.
The larger mapping spaces are auxiliary; original values remain small.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationCoherentSquare
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : FramedResolution C) (Y V : ResolutionObject C) (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V)

abbrev Context := MixedChoiceFunctor.Context X V
abbrev contexts : Context X V ⥤ MixedChoiceFunctor.Context X Y :=
  (𝟭 (Over X)ᵒᵖ).prod (Under.map g)
abbrev values : Context X V ⥤ SSet.{v} := contexts X Y V g ⋙ MixedChoiceFunctor.functor X Y f hcof

include hfib in
lemma valueFillers (t : Context X V) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers ((values hcof X Y V f g).obj t) := by
  intro n a
  let e := AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom
  obtain ⟨b, hb⟩ := AllFactorizationPre.fillers hcof hfib t.1.unop.hom.map f (g ≫ t.2.hom)
    (FramedResolution.frameMap t.1.unop.hom) n (a ≫ e.hom)
  refine ⟨b ≫ e.inv, ?_⟩
  rw [← Category.assoc, hb, Category.assoc, e.hom_inv_id]
  exact Category.comp_id a

abbrev triangleParameter := AnchoredChain.simplicial g ⊗
  SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)
abbrev diagonalParameter : AnchoredChain.simplicial g ⊗
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ triangleParameter Y V g :=
  AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (1 : Fin 3)
abbrev squareParameter : SSet.{max u v} :=
  pushout (diagonalParameter Y V g) (diagonalParameter Y V g)

abbrev side (left : Bool) : triangleParameter Y V g ⟶ squareParameter Y V g :=
  if left then pushout.inl _ _ else pushout.inr _ _

abbrev oldTriangle (left : Bool) (t : Context X V) : triangleParameter Y V g ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values hcof X Y V f g).obj t) :=
  AllFactorizationMixedContext.triangle hcof hfib t.1.unop.hom f g t.2.hom left

/-- Glue the already selected entire triangles before making any external choice. -/
def oldSquare (t : Context X V) : squareParameter Y V g ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values hcof X Y V f g).obj t) :=
  pushout.desc (oldTriangle hcof hfib X Y V f g true t)
    (oldTriangle hcof hfib X Y V f g false t)
    (AllFactorizationMixedContext.common_diagonal hcof hfib t.1.unop.hom f g t.2.hom)

lemma oldSquare_side (left : Bool) (t : Context X V) : side Y V g left ≫
    oldSquare hcof hfib X Y V f g t = oldTriangle hcof hfib X Y V f g left t := by
  cases left
  · exact pushout.inr_desc _ _ _
  · exact pushout.inl_desc _ _ _

/-- One coherent system on the whole glued all-factorization square. -/
def square : NerveLargeParameter.System (values hcof X Y V f g) (squareParameter Y V g) :=
  NerveLargeParameter.extendFamilies (values hcof X Y V f g)
    (valueFillers hcof hfib X Y V f g) (squareParameter Y V g) (oldSquare hcof hfib X Y V f g)

lemma square_evaluate (t : Context X V) :
    NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted (values hcof X Y V f g))
      (square hcof hfib X Y V f g) t = oldSquare hcof hfib X Y V f g t :=
  NerveLargeParameter.extendFamilies_evaluate _ _ _ _ t

def triangle (left : Bool) : NerveLargeParameter.System (values hcof X Y V f g)
    (triangleParameter Y V g) :=
  NerveLargeParameter.restrict (values hcof X Y V f g)
    (square hcof hfib X Y V f g) (side Y V g left)

lemma triangle_evaluate (left : Bool) (t : Context X V) :
    NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted (values hcof X Y V f g))
      (triangle hcof hfib X Y V f g left) t = oldTriangle hcof hfib X Y V f g left t := by
  rw [triangle, NerveLargeParameter.restrict_evaluate, square_evaluate, oldSquare_side]

lemma shared_diagonal :
    NerveLargeParameter.restrict (values hcof X Y V f g) (triangle hcof hfib X Y V f g true)
      (diagonalParameter Y V g) =
    NerveLargeParameter.restrict (values hcof X Y V f g) (triangle hcof hfib X Y V f g false)
      (diagonalParameter Y V g) := by
  rw [triangle, triangle, NerveLargeParameter.restrict_comp, NerveLargeParameter.restrict_comp]
  exact congrArg (NerveLargeParameter.restrict (values hcof X Y V f g)
    (square hcof hfib X Y V f g)) (pushout.condition)

/-- Recover the originally selected square in its old choice-space coordinates. -/
lemma triangle_recover (left : Bool) (t : Context X V) :
    NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted (values hcof X Y V f g))
      (triangle hcof hfib X Y V f g left) t ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    AllFactorizationMixed.triangle hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) left := by
  rw [triangle_evaluate]
  exact AllFactorizationMixedContext.triangle_recover hcof hfib t.1.unop.hom f g t.2.hom left

/-- All global homotopy edges are restrictions of the same whole coherent square. -/
def edge (left : Bool) (k : Fin 3) : NerveLargeParameter.System (values hcof X Y V f g)
    (AnchoredChain.simplicial g ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) :=
  NerveLargeParameter.restrict (values hcof X Y V f g) (triangle hcof hfib X Y V f g left)
    (AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ k)

lemma edge_recover (left : Bool) (k : Fin 3) (t : Context X V) :
    NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted (values hcof X Y V f g))
      (edge hcof hfib X Y V f g left k) t ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ k ≫
      AllFactorizationMixed.triangle hcof hfib t.1.unop.hom.map f g t.2.hom
        (FramedResolution.frameMap t.1.unop.hom) left := by
  rw [edge, NerveLargeParameter.restrict_evaluate, Category.assoc, triangle_recover]

/-- Finite parameter evaluation still gives an actual simplex in the original small value. -/
def simplex (left : Bool) (t : Context X V) {n : ℕ} (c : AnchoredChain g n)
    (q : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      AllFactorizationMixed.choiceSpace t.1.unop.hom.map f g t.2.hom
        (FramedResolution.frameMap t.1.unop.hom) :=
  SSet.yonedaEquiv.symm (((NerveParameterExtension.evaluate
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted (values hcof X Y V f g)) (triangle hcof hfib X Y V f g left) t ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
        (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom).app
    (Opposite.op (SimplexCategory.mk n)) (c, q)).down)

lemma simplex_recover (left : Bool) (t : Context X V) {n : ℕ} (c : AnchoredChain g n)
    (q : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    simplex hcof hfib X Y V f g left t c q =
      AllFactorizationMixed.simplex hcof hfib t.1.unop.hom.map f g t.2.hom
        (FramedResolution.frameMap t.1.unop.hom) left c q := by
  unfold simplex
  rw [triangle_recover]
  rfl

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationCoherentSquare
