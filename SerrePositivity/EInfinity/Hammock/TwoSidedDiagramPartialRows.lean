module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramRows
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonalMap
public import SerrePositivity.EInfinity.Hammock.TripleSimplicialDiagonal
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialColumnWeak

/-!
# 元の単体的二方向図式の射列長を固定した部分対角

概要：元の全圏の対角比較を、固定射列長ごとの元の部分対角の弱比較へ還元する。
方針：三重対角の元の同型と列の弱同値による対角判定を使う。
規約：底や係数の各通常次数での弱同値性は要求しない。
使われ方：DK10.6(ii)の固定対象列ごとの Hom 因子による判定。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory SerrePositivity.InfinityCategories

variable (D : SimplicialObject Data.{u})

def partialRows : SimplicialObject SSet.{u} :=
  TripleSimplicial.partialDiagonalFunctor.obj (D ⋙ rowsFunctor)

def partialRowsIso : DoubleSimplicial.diagonalFunctor.obj (partialRows D) ≅ diagonalBar D :=
  TripleSimplicial.fullDiagonalIso (D ⋙ rowsFunctor)

def chainRow (n : SimplexCategoryᵒᵖ) : SSet.{u} := (partialRows D).flip.obj n

variable {D} {E : SimplicialObject Data.{u}} (τ : D ⟶ E)

def partialRowsMap : partialRows D ⟶ partialRows E :=
  TripleSimplicial.partialDiagonalFunctor.map (Functor.whiskerRight τ rowsFunctor)

def chainRowMap (n : SimplexCategoryᵒᵖ) : chainRow D n ⟶ chainRow E n :=
  ((flipFunctor _ _ _).map (partialRowsMap τ)).app n

lemma partialRowsIso_naturality :
    DoubleSimplicial.diagonalFunctor.map (partialRowsMap τ) ≫ (partialRowsIso E).hom =
      (partialRowsIso D).hom ≫ diagonalBarMap τ := by
  ext n e
  rfl

lemma diagonalTotalMap_weak_of_chainRows
    (h : ∀ n, IsWeakHomotopyEquivalence (chainRowMap τ n)) :
    IsWeakHomotopyEquivalence (diagonalTotalMap τ) := by
  apply (diagonalMap_weak_iff τ).mpr
  have hc := (DoubleSimplicial.diagonalFunctor_map_weak_of_columns
    (partialRowsMap τ) h).comp
      (isPrecompositionEquivalence_of_iso (partialRowsIso E)).isWeakHomotopyEquivalence
  rw [partialRowsIso_naturality τ] at hc
  have hd := (isPrecompositionEquivalence_of_iso (partialRowsIso D)).isWeakHomotopyEquivalence
  exact hd.cancel_left hc

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
