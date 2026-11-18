module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyPrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent

/-!
概要：対象と射の宇宙が異なる圏の自然変換の nerve 円柱。
方針：標準区間と元の射列の積を自然変換の uncurry に合成する。
規約：HTT 6.2.2.7・5.5.4.15 の集合値層化単位に用いる通常の nerve の計算。
使われ方：同じ自然変換を空間値前層の層化比較へ送る。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 通常の nerve 上で自然変換を表す時間を第一因子に置いた円柱。 -/
def largeNerveNatTransPrism {A : Type v} [Category.{u} A] {F G : A ⥤ A} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve A ⟶ nerve A where
  app n := ↾fun z => ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- 圏の対象と射の宇宙を分けて、同じ自然変換の全 nerve 円柱を作る。 -/
@[cite HTT "6.2.2.7" (partial := special) "集合値層化の単位を通常の nerve の円柱で読む。"]
def largeNerveNatTransHomotopy :
    ∀ {A : Type v} [Category.{u} A] {F G : A ⥤ A} (η : F ⟶ G),
      SSet.Homotopy (nerveMap F) (nerveMap G) := by
  intro A hA F G η
  refine homotopyOfPrism (largeNerveNatTransPrism η) ?_ ?_
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    case h_map =>
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change 𝟙 _ ≫ F.map (s.map f) = F.map (s.map f)
      exact Category.id_comp _
    case h_obj =>
      intro i
      rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    case h_map =>
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change 𝟙 _ ≫ G.map (s.map f) = G.map (s.map f)
      exact Category.id_comp _
    case h_obj =>
      intro i
      rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
