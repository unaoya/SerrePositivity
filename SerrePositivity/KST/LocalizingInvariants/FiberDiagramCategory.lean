module

public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering

/-!
概要：実 fiber 正方形を対象、関手 ∞ 圏のホモトピー圏の射を比較とする圏。
方針：元の零角と pullback 性を保持し、全正方形の比較を評価して通常の自然変換にする。
規約：四辺の可換式だけを比較の入力にしない。使われ方：pro fiber 図式の塔と遷移。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

structure FiberDiagram where
  triangle : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u}
  isFiber : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence triangle

namespace FiberDiagram

def diagramVertex (D : FiberDiagram.{u}) :
    hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj Sp.{u}) :=
  HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D.triangle.square)

instance : Category FiberDiagram.{u} where
  Hom D E := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom D.triangle.square E.triangle.square
  id D := 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D.triangle.square))
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def diagramFunctor : FiberDiagram.{u} ⥤
    (hoFunctor.obj ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⥤ hoFunctor.obj Sp.{u}) where
  obj D := (hoFunctor.map D.triangle.square).toFunctor
  map {D E} f := (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj D.triangle.square)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation _ _).map f ≫
      (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj E.triangle.square)).hom
  map_id D := by
    change (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj D.triangle.square)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation _ _).map
        (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D.triangle.square))) ≫
        (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj D.triangle.square)).hom = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp {D E F} f g := by
    change (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj D.triangle.square)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation _ _).map
        ((f : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom D.triangle.square E.triangle.square) ≫ g) ≫
        (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj F.triangle.square)).hom = _
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

def vertex (i j : Fin 2) : FiberDiagram.{u} ⥤ hoFunctor.obj Sp.{u} where
  obj D := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex D.triangle.square i j
  map {D E} f := (diagramFunctor.map f).app
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) i j)
  map_id D := by rw [diagramFunctor.map_id]; rfl
  map_comp f g := by rw [diagramFunctor.map_comp]; rfl

def inclusion : vertex.{u} 0 0 ⟶ vertex 1 0 where
  app D := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom D.triangle.square
  naturality {_D _E} f :=
    ((diagramFunctor.map f).naturality
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))).symm

def projection : vertex.{u} 1 0 ⟶ vertex 1 1 where
  app D := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight D.triangle.square
  naturality {_D _E} f :=
    ((diagramFunctor.map f).naturality
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])))).symm

end FiberDiagram
end SerrePositivity.KST.LocalizingInvariants
