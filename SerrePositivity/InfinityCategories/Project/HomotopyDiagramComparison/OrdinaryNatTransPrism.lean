module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyPrism
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：元の通常の自然変換を、元の通常の nerve 上の区間族で表す。
方針：二点図式を uncurry し、元の全射列との直積へ適用する。
規約：対象の宇宙 v と Hom の宇宙 u を分離する。使われ方：元の cf 置換の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable {C D : Type v} [Category.{u} C] [Category.{u} D]

/-- 元の通常の自然変換を、同じ元の nerve 関手を両端とする prism へ写す。 -/
def ordinaryNatTransPrism {F G : C ⥤ D} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve C ⟶ nerve D where
  app n := ↾fun z ↦ ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 元の自然変換の prism の始点は、元の始域関手の nerve である。 -/
lemma ordinaryNatTransPrism_zero {F G : C ⥤ D} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve C) ≫ ordinaryNatTransPrism η = nerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Φ
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (Φ.map _) = F.map (Φ.map _)
    simp only [Category.id_comp]

/-- 元の自然変換の prism の終点は、元の終域関手の nerve である。 -/
lemma ordinaryNatTransPrism_one {F G : C ⥤ D} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve C) ≫ ordinaryNatTransPrism η = nerveMap G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Φ
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ G.map (Φ.map _) = G.map (Φ.map _)
    simp only [Category.id_comp]

/-- 元の自然変換の各頂点の辺は、元の指定成分の通常の nerve の辺である。 -/
lemma ordinaryNatTransPrism_vertexEdge {F G : C ⥤ D} (η : F ⟶ G) (x : C) :
    (ordinaryNatTransPrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) 1) = (nerve.edgeMk (η.app x)).edge := by
  apply ComposableArrows.ext₁
  case left => rfl
  case right => rfl
  case w =>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app x ≫ G.map (𝟙 x) = η.app x
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
