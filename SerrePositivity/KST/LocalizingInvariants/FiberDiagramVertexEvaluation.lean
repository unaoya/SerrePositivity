module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramModelComparison

/-!
概要：実 fiber 図式の頂点関手を、元の全四角形の関手圏の評価と自然に比較する。
方針：全図式の包含を明示し、復号した頂点の等号による輸送を使う。
規約：比較は任意の図式間の射に対して自然。四辺だけの比較では代用しない。
使われ方：loop 四角形の全族の接続射を元の評価関手へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

def diagramInclusion : FiberDiagram.{u} ⥤
    hoFunctor.obj ((ihom ((Δ[1] : SSet.{u+1}) ⊗ Δ[1])).obj Sp.{u}) where
  obj := diagramVertex
  map f := f

lemma vertexEvaluationObj_eq (D : FiberDiagram.{u}) (i j : Fin 2) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{u})
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor.obj
        (diagramVertex D) = (vertex i j).obj D := by
  apply Truncated.HomotopyCategory.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) D.triangle.square

def vertexEvaluationIso (i j : Fin 2) :
    diagramInclusion.{u} ⋙ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (Y := Sp.{u}) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor ≅
        vertex i j :=
  NatIso.ofComponents (fun D => eqToIso (vertexEvaluationObj_eq D i j)) (by
    intro D E f
    change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (Y := Sp.{u}) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor.map f ≫
      _ = _ ≫ (vertex i j).map f
    rw [vertex_map_evaluate]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate, eqToIso.hom, eqToHom_refl]
    let m := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (Y := Sp.{u}) (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor.map f
    change m ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ m ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id])

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
