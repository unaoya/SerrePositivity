module

public import Mathlib.CategoryTheory.Functor.Currying
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：通常の自然変換をサイズ調整した strict coherent 図式の円柱にする。
方針：自然変換の二点図式を uncurry してから coherent nerve に送る。
規約：対象と Hom の宇宙の違う単体的圏を許す。
使われ方：Cat_∞ 内での path 置換の前後の図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：自然変換をサイズ調整した通常の nerve 上の円柱へ送る。
方針：二点順序圏の矢印を uncurry し、時刻と元の射列の積を前合成する。
規約：標的の対象宇宙 v と Hom 宇宙 u を分ける。
使われ方：Cat_∞ 値の図式の比較を実際のホモトピーにする。 -/
def resizedNatTransMap {F G : I ⥤ C} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v,u}).obj (nerve I) ⟶ nerve C where
  app n := ↾fun z ↦ ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2.down) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- 概要：自然変換を strict coherent 図式間の円柱へ送る。
方針：通常の nerve の円柱に F1 の coherent 表示を後合成する。
規約：始域は ULift N(I)、時刻の標準区間は第一因子。
使われ方：元の cospan と path 置換後の cospan の比較。 -/
def strictCoherentNatTransMap {F G : I ⥤ C} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v,u}).obj (nerve I) ⟶ SimplicialNerve C :=
  resizedNatTransMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C
/-- 概要：自然変換の円柱の先頭は元の始域図式。
方針：順序図式の対象と射を比較し、恒等自然変換の成分を消す。
規約：指定された F 自体との厳密な等式。
使われ方：図式の同型への円柱の束ね。 -/
lemma strictCoherentNatTransMap_zero {F G : I ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 ((SSet.uliftFunctor.{v,u}).obj (nerve I)) ≫ strictCoherentNatTransMap η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    change F.obj (s.down.obj i.down) = F.obj (s.down.obj i.down)
    rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (s.down.map _) = F.map (s.down.map _)
    simp
/-- 概要：自然変換の円柱の終端は元の終域図式。
方針：順序図式の対象と射を比較し、恒等自然変換の成分を消す。
規約：指定された G 自体との厳密な等式。
使われ方：図式の同型への円柱の束ね。 -/
lemma strictCoherentNatTransMap_one {F G : I ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((SSet.uliftFunctor.{v,u}).obj (nerve I)) ≫ strictCoherentNatTransMap η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    change G.obj (s.down.obj i.down) = G.obj (s.down.obj i.down)
    rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ G.map (s.down.map _) = G.map (s.down.map _)
    simp

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
