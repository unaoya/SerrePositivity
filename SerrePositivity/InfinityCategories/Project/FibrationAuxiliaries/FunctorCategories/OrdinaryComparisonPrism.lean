module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexStandardSection
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：通常の自然変換を nerve 上の全次数の prism にする。
方針：二点の関手図式を uncurry し、頂点列と単体の積を評価する。
規約：自然変換の成分を選び直さない。
使われ方：標準単体の初頂点切断の比較を coherent な比較へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 通常の自然変換の、単体的な区間を用いた実際の prism。 -/
def ordinaryComparisonPrism {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun s ↦ (s.2.down.toOrderHom.monotone.functor.prod' s.1) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 自然変換の prism の先頭は、元の始域関手の nerve。 -/
lemma ordinaryComparisonPrism_zero {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : SSet.ι₀ ≫ ordinaryComparisonPrism η = nerveMap F := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ ?_)
  change (𝟙 F : F ⟶ F).app _ ≫ F.map (σ.map f) =
    𝟙 _ ≫ F.map (σ.map f) ≫ 𝟙 _
  simp

/-- 自然変換の prism の終端は、元の標的関手の nerve。 -/
lemma ordinaryComparisonPrism_one {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : SSet.ι₁ ≫ ordinaryComparisonPrism η = nerveMap G := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ ?_)
  change (𝟙 G : G ⟶ G).app _ ≫ G.map (σ.map f) =
    𝟙 _ ≫ G.map (σ.map f) ≫ 𝟙 _
  simp

/-- 自然変換が定める全次数で整合する単体的ホモトピー。 -/
def ordinaryComparisonHomotopy {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := ordinaryComparisonPrism η
  h₀ := ordinaryComparisonPrism_zero η
  h₁ := ordinaryComparisonPrism_one η
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- prism の頂点での縦辺は、指定した自然変換の成分そのもの。 -/
lemma ordinaryComparisonHomotopy_vertex {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (ordinaryComparisonHomotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).edge =
      (nerve.edgeMk (η.app c)).edge := by
  change (ordinaryComparisonPrism η).app _
    ((nerve C).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      ComposableArrows.mk₁ (η.app c)
  refine ComposableArrows.ext₁
    (F := (ordinaryComparisonPrism η).app _
      ((nerve C).σ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
    (G := ComposableArrows.mk₁ (η.app c)) rfl rfl ?_
  change η.app c ≫ G.map (𝟙 c) = 𝟙 _ ≫ η.app c ≫ 𝟙 _
  simp

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
