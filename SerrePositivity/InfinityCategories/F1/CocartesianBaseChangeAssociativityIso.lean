module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityEdgeEvaluation
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeJointComparisonIso

/-!
概要：元の二回の底変換と直接の底変換の分類像の、全 fibration の同じ関手同型。
方針：同じ比較の辺を二変数で評価し、元の結合同型の可逆性を回収する。
規約：元の全対象・全高次 Hom の共同の比較の辺そのものを用いる。
使われ方：同じ分類 Hom 比較 span の合成の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ全 fibration の結合比較の辺は、元の成分の同型性によって可逆。 -/
lemma cocartesianBaseChangeAssociativityEdge_isInvertible :
    IsInvertibleEdge (cocartesianBaseChangeAssociativityEdge l k).toTruncated := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt
    (cocartesianBaseChangeAssociativityEdge l k).toTruncated).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  change IsInvertibleEdge (functorEdgeAt (cocartesianBaseChangeAssociativityEdge l k)
    (coherentNerveVertex (coherentNerveObject s))).toTruncated
  apply (isInvertibleEdge_iff_evaluateFunctorAt_vertices
    (functorEdgeAt (cocartesianBaseChangeAssociativityEdge l k)
      (coherentNerveVertex (coherentNerveObject s)))).mpr
  rintro ⟨v⟩
  obtain ⟨a, rfl⟩ : ∃ a : A, v = nerveVertex a :=
    ⟨v.obj 0, ComposableArrows.ext₀ rfl⟩
  apply (isInvertibleEdge_congr
    (cocartesianBaseChangeAssociativityEdge_at l k (coherentNerveObject s) a)).mpr
  exact coherentQCatEdge_isInvertible_of_isQCatEquivalence
    (cocartesianBaseChangeAssociativityQCat_isQCatEquivalence
      (coherentNerveObject s).val.hom l k a)

/-- 二回と直接の底変換の、元の同じ分類主写像への合成は全体の関手として同型。 -/
def cocartesianBaseChangeAssociativityIso :
    FunctorIso
      (cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianFibrationInfinityBaseChange (nerveMap l) ≫
          cocartesianStraighteningCoherentMap A)
      (cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
        cocartesianStraighteningCoherentMap A) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (cocartesianBaseChangeAssociativityEdge l k).toTruncated) :=
    cocartesianBaseChangeAssociativityEdge_isInvertible l k
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (cocartesianBaseChangeAssociativityEdge l k).toTruncated)

end SerrePositivity.InfinityCategories
