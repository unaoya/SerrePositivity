module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationPostPoints
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationChoices
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.HomotopyEndpointComparison

/-!
# 中断した任意モデル源への一般化：AllFactorizationPostRelative

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Postcomposition comparison relative to every prescribed factorization point。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0055][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0055
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Postcomposition comparison relative to every prescribed factorization point

The new comparison fixes all factorization vertices. The previously chosen
comparison is retained and compared to the new one relative to both entire
endpoint families.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V W : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

abbrev vertexMap : NerveVertices.vertices.{v, max u v} (ArrowFactorization g) ⟶
    NerveVertices.vertices.{v, max u v} (ArrowFactorization (g ≫ b)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap (fun p : ULift.{v} (ArrowFactorization g) =>
    (⟨(ArrowFactorization.postTo g b (g ≫ b) rfl).obj p.down⟩ :
      ULift.{v} (ArrowFactorization (g ≫ b))))

omit [ModelCategory SSet.{v}] in
lemma vertex_square : NerveVertices.inclusion (ArrowFactorization g) ≫
    nerveMap (ArrowFactorization.postTo g b (g ≫ b) rfl) =
      vertexMap g b ≫ NerveVertices.inclusion (ArrowFactorization (g ≫ b)) := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun p => ?_)
  refine ComposableArrows.ext (fun _ => rfl) ?_
  intro i hi
  change (ArrowFactorization.postTo g b (g ≫ b) rfl).map (𝟙 p.down) = _
  simp only [CategoryTheory.Functor.map_id, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma liftedPoint_post (p : ArrowFactorization g) :
    AllFactorizationComparison.liftedPoint hcof f (g ≫ b)
        ((ArrowFactorization.postTo g b (g ≫ b) rfl).obj p) =
      AllFactorizationComparison.liftedPoint hcof f g p ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
        (CoherentLiftPostComposition.firstMap hcof X Y V W f g b) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso.{u, v} 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map _ = _
  rw [AllFactorizationPostPoints.point_post, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp, Category.assoc]

lemma vertexData_post : vertexMap g b ≫ AllFactorizationComparison.vertexData hcof f (g ≫ b) =
    AllFactorizationComparison.vertexData hcof f g ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
      (CoherentLiftPostComposition.firstMap hcof X Y V W f g b) := by
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap _ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap _ ≫ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap_pointsMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap_postcomp]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap
  funext p
  exact liftedPoint_post hcof f g b p.down

abbrev vertexInclusion : NerveVertices.vertices.{v, max u v} (ArrowFactorization g) ⟶
    AnchoredChain.simplicial g :=
  NerveVertices.inclusion (ArrowFactorization g) ≫ (AnchoredChain.nerveIso g).hom

instance : Mono (vertexInclusion g) := inferInstanceAs (Mono (_ ≫ _))

abbrev vertexBoundary := AllFactorizationComparison.vertexData hcof f g ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
  (CoherentLiftPostComposition.firstMap hcof X Y V W f g b)

lemma direct_vertices : vertexInclusion g ≫ AllFactorizationPost.direct hcof hfib f g b =
    vertexBoundary hcof f g b := by
  simp only [vertexInclusion, AllFactorizationPost.direct, AnchoredChain.mapFunctor,
    AllFactorizationComparison.chainComparison, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, vertex_square, Category.assoc,
    AllFactorizationComparison.comparison_vertices, vertexData_post]

lemma transported_vertices : vertexInclusion g ≫ AllFactorizationPost.transported hcof hfib f g b =
    vertexBoundary hcof f g b := by
  simp only [vertexInclusion, AllFactorizationPost.transported,
    AllFactorizationComparison.chainComparison, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, AllFactorizationComparison.comparison_vertices]

/-- A global postcomposition homotopy fixing every original factorization point. -/
def homotopy : SSet.Homotopy (AllFactorizationPost.direct hcof hfib f g b)
    (AllFactorizationPost.transported hcof hfib f g b) :=
  LargeParameterRelativeChoice.homotopy (AllFactorizationPost.fillers hcof hfib f g b)
    (vertexInclusion g) (vertexBoundary hcof f g b)
    (AllFactorizationPost.direct hcof hfib f g b) (AllFactorizationPost.transported hcof hfib f g b)
    (direct_vertices hcof hfib f g b) (transported_vertices hcof hfib f g b)

lemma fixed_vertices : vertexInclusion g ▷ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
    (homotopy hcof hfib f g b).h =
      NerveVertices.vertices (ArrowFactorization g) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ vertexBoundary hcof f g b :=
  LargeParameterRelativeChoice.homotopy_relative _ _ _ _ _ _ _

/-- Retain the old selected homotopy as an entire face, relative to both endpoints. -/
abbrev oldComparison : SSet.Homotopy (AllFactorizationPost.homotopy hcof hfib f g b).h
    (homotopy hcof hfib f g b).h :=
  HomotopyEndpointComparison.homotopy (AllFactorizationPost.fillers hcof hfib f g b)
    (AllFactorizationPost.homotopy hcof hfib f g b) (homotopy hcof hfib f g b)

lemma oldComparison_fixed_endpoints :
    (AnchoredChain.simplicial g ◁ (SSet.boundary.{max u v} 1).ι) ▷
        SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
        (oldComparison hcof hfib f g b).h =
      (AnchoredChain.simplicial g ⊗ (SSet.boundary.{max u v} 1).toSSet) ◁
          (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ LargeParameterHomotopy.boundaryMap
          (AllFactorizationPost.direct hcof hfib f g b)
          (AllFactorizationPost.transported hcof hfib f g b) :=
  HomotopyEndpointComparison.fixed_endpoints _ _ _

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostRelative
