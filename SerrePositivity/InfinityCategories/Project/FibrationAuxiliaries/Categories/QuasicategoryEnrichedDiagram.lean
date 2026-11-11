module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory

/-!
概要：全 Hom に自然な quasicategory 値豊穣関手の比較を、底全体の図式へ束ねる。
方針：各対象の元の図式と、全高次 Hom の各成分の作用を保持する。
規約：値や全変換空間の Kan 性を要求しない。
使われ方：底変換比較を底の全対象・全射で同時に実現する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 概要：quasicategory 値豊穣関手と豊穣自然な比較の通常の図式。
方針：比較の恒等・合成を全対象で厳密に保持する。
規約：自然性は全高次の豊穣 Hom に関する。
使われ方：比較の列を同時に coherent nerve へ実現する入力。 -/
structure QuasicategoryEnrichedDiagram (C : Type v) [Category.{u} C] [SimplicialCategory C]
    (J : Type u) [Category.{u} J] where
  obj : J → EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}
  map : ∀ {i j : J}, (i ⟶ j) → _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (obj i) (obj j)
  map_id : ∀ i X, (map (𝟙 i)).val X = 𝟙 ((obj i).obj X)
  map_comp : ∀ {i j k : J} (f : i ⟶ j) (g : j ⟶ k) X,
    (map (f ≫ g)).val X = (map f).val X ≫ (map g).val X

/-- 概要：比較の図式を一つの対象で評価して通常の quasicategory 値図式にする。
方針：図式に記録した恒等・合成の条件をそのまま使う。
規約：対象の図式を独立に選ばない。
使われ方：図式値豊穣関手の対象への作用。 -/
def QuasicategoryEnrichedDiagram.evaluate {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) (X : C) : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj j := (D.obj j).obj X
  map f := (D.map f).val X
  map_id j := D.map_id j X
  map_comp f g := D.map_comp f g X

/-- 概要：一つの高次 Hom の単体は全成分で整合する strict な変換を与える。
方針：各成分の豊穣作用と比較の豊穣自然性を使う。
規約：添字圏の全ての射に関して自然。
使われ方：Kan 図式値の豊穣 Hom の作用の単体。 -/
def QuasicategoryEnrichedDiagram.mappingSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) (X Y : C)
    {n : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (D.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
      (D.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) n := by
  refine ⟨fun j ↦ ((D.obj j).map X Y).app n θ, ?_⟩
  intro i j f k α x
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryEnrichedComparison_app (D.map f) X Y θ α x).symm

/-- 概要：豊穣 Hom を図式間の全 strict 変換空間へ写す。
方針：各成分の単体的自然性を同時に適用する。
規約：頂点の射だけへの制限は行わない。
使われ方：図式値豊穣関手の Hom の作用。 -/
def QuasicategoryEnrichedDiagram.mappingSpaceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) (X Y : C) :
    SimplicialCategory.sHom X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (D.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) (D.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) where
  app _ := ↾D.mappingSimplex X Y
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext j
    exact congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
      ((ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Y).obj).obj m ↦ f θ)
      (((D.obj j).map X Y).naturality α)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
