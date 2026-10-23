module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityFamily
public import SerrePositivity.InfinityCategories.F1.QCatDiagramArrowCurry

/-!
概要：元の二回の底変換と直接の底変換の分類像の間の、同じ結合比較の実際の辺。
方針：元の共同実現を区間族へ curry し、同じ標準区間の辺で転置する。
規約：両端は元の底変換 ∞ 関手に続く元の分類主写像そのもの。
使われ方：同じ Hom 比較 span の結合に必要な coherent な族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合比較の全 fibration の区間族。 -/
def cocartesianBaseChangeAssociativityIntervalFamily :
    CocartesianFibrationInfinity (nerve C) ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  cocartesianBaseChangeAssociativityFamily l k ≫ qCatDiagramArrowCurry A

/-- 同じ区間族の零端点は、二回の元の底変換に続く同じ分類。 -/
lemma cocartesianBaseChangeAssociativityIntervalFamily_zero :
    cocartesianBaseChangeAssociativityIntervalFamily l k ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianFibrationInfinityBaseChange (nerveMap l) ≫
        cocartesianStraighteningCoherentMap A := by
  rw [cocartesianBaseChangeAssociativityIntervalFamily, Category.assoc,
    qCatDiagramArrowCurry_endpoint]
  exact cocartesianBaseChangeAssociativityFamily_zero l k

/-- 同じ区間族の一端点は、直接の元の底変換に続く同じ分類。 -/
lemma cocartesianBaseChangeAssociativityIntervalFamily_one :
    cocartesianBaseChangeAssociativityIntervalFamily l k ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
      cocartesianStraighteningCoherentMap A := by
  rw [cocartesianBaseChangeAssociativityIntervalFamily, Category.assoc,
    qCatDiagramArrowCurry_endpoint]
  exact cocartesianBaseChangeAssociativityFamily_one l k

/-- 二回と直接の底変換の元の分類像を両端に持つ、同じ結合比較の辺。 -/
def cocartesianBaseChangeAssociativityEdge :
    Edge (functorVertex (cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianFibrationInfinityBaseChange (nerveMap l) ≫
        cocartesianStraighteningCoherentMap A))
      (functorVertex (cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
        cocartesianStraighteningCoherentMap A)) :=
  ((SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k))).ofEq
    (by rw [transposeFunctorFamily_vertex, cocartesianBaseChangeAssociativityIntervalFamily_zero])
    (by rw [transposeFunctorFamily_vertex, cocartesianBaseChangeAssociativityIntervalFamily_one])

end SerrePositivity.InfinityCategories
