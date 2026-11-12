module

public import SerrePositivity.KST.LocalizingInvariants.StrictConeMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans

/-!
概要：Hom より大きい添字圏の自然変換を、同じサイズの coherent prism にする。
方針：合成可能射列と二点の関手で自然変換を評価する。
規約：添字圏と値域の Hom の宇宙を分ける。使われ方：始対象を加えた BF 錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

variable {J : Type (max u v)} [SmallCategory J]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

def largeNervePrism {F G : J ⥤ C} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve J ⟶ nerve C where
  app n := ↾fun z ↦ ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- 概要：自然変換を strict coherent 図式間の円柱へ送る。
方針：通常の nerve の円柱に F1 の coherent 表示を後合成する。
規約：始域は nerve J、時刻の標準区間は第一因子。
使われ方：元の cospan と path 置換後の cospan の比較。 -/
def largeCoherentPrism {F G : J ⥤ C} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve J ⟶ SimplicialNerve C :=
  largeNervePrism η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C
/-- 概要：自然変換の円柱の先頭は元の始域図式。
方針：順序図式の対象と射を比較し、恒等自然変換の成分を消す。
規約：指定された F 自体との厳密な等式。
使われ方：図式の同型への円柱の束ね。 -/
lemma largeCoherentPrism_zero {F G : J ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve J) ≫ largeCoherentPrism η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    change F.obj (s.obj i.down) = F.obj (s.obj i.down)
    rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (s.map _) = F.map (s.map _)
    simp
/-- 概要：自然変換の円柱の終端は元の終域図式。
方針：順序図式の対象と射を比較し、恒等自然変換の成分を消す。
規約：指定された G 自体との厳密な等式。
使われ方：図式の同型への円柱の束ね。 -/
lemma largeCoherentPrism_one {F G : J ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve J) ≫ largeCoherentPrism η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  congr 1
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    change G.obj (s.obj i.down) = G.obj (s.obj i.down)
    rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ G.map (s.map _) = G.map (s.map _)
    simp


end SerrePositivity.KST.LocalizingInvariants.StrictConeMap
