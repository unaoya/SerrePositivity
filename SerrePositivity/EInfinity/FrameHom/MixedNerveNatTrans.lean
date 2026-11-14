module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveULiftHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyComponentPrecomp
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# 対象と Hom の宇宙が異なる通常圏の元の自然変換円柱

概要：対象が大きい通常圏の同じ自然変換を全単体のホモトピーへ移す。
方針：Hom のみを上げた元の円柱を、そのまま元の nerve へ引き戻す。
規約：元の対象・元の射・指定自然変換を保持する。
使われ方：全代数の置換比較と離散入力の全関手比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]

def up (C : Type (u + 1)) [Category.{u} C] : nerve C ⟶ nerve (ULiftHom.{u + 1} C) where
  app _ := ↾fun Γ => Γ ⋙ ULiftHom.up.{u, u + 1, u + 1}
  naturality _ _ _ := rfl

def down (C : Type (u + 1)) [Category.{u} C] : nerve (ULiftHom.{u + 1} C) ⟶ nerve C where
  app _ := ↾fun Γ => Γ ⋙ ULiftHom.down.{u, u + 1, u + 1}
  naturality _ _ _ := rfl

def lifted (F : C ⥤ D) : ULiftHom.{u + 1} C ⥤ ULiftHom.{u + 1} D :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ F ⋙ ULiftHom.up.{u, u + 1, u + 1}

def liftedNatTrans {F G : C ⥤ D} (η : F ⟶ G) : lifted F ⟶ lifted G :=
  Functor.whiskerLeft ULiftHom.down.{u, u + 1, u + 1}
    (Functor.whiskerRight η ULiftHom.up.{u, u + 1, u + 1})

lemma recover (F : C ⥤ D) :
    (up C ≫ nerveMap (lifted F)) ≫ down D = nerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change ((Γ ⋙ ULiftHom.up.{u, u + 1, u + 1}) ⋙
      (ULiftHom.down.{u, u + 1, u + 1} ⋙ F ⋙ ULiftHom.up.{u, u + 1, u + 1})) ⋙
      ULiftHom.down.{u, u + 1, u + 1} = Γ ⋙ F
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def homotopy {F G : C ⥤ D} (η : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (HomotopyClasses.postHomotopy (down D)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans η)) (up C)))
    (recover F) (recover G)

lemma up_vertex (i : C) : (up C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp i : ULiftHom.{u + 1} C) := ComposableArrows.ext₀ rfl

lemma down_mk₁ {i j : ULiftHom.{u + 1} D} (f : i ⟶ j) :
    (down D).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (ULiftHom.down.{u, u + 1, u + 1}.map f) := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma homotopy_component {F G : C ⥤ D} (η : F ⟶ G) (i : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge =
      (nerve.edgeMk (η.app i)).edge := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans η)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyComponent_precomp_edge H (up C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
  rw [up_vertex] at hp
  have hc := hp.trans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component
    (liftedNatTrans η) (ULiftHom.objUp i))
  have h := congrArg ((down D).app (Opposite.op ⦋1⦌)) hc
  change (down D).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (up C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge = _
  refine h.trans ?_
  change (down D).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((liftedNatTrans η).app (ULiftHom.objUp i))) =
      ComposableArrows.mk₁ (η.app i)
  rw [down_mk₁]
  rfl

end SerrePositivity.EInfinity.FrameHom.MixedNerve
