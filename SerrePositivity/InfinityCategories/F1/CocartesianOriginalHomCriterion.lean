module

public import SerrePositivity.InfinityCategories.F1.CocartesianStraighteningHomInterval
public import SerrePositivity.InfinityCategories.F1.CocartesianStraighteningVertices
public import SerrePositivity.InfinityCategories.F1.CoherentHomEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostHomCriterion

/-!
概要：元の cocartesian Hom の区間作用の同値性を、同じ分類主写像の充満忠実性へ戻す。
方針：作用を元の分類写像の pinched Hom の後合成と同定し、標準比較を消去する。
規約：元の相対 Hom と元の分類主写像を固定する。
使われ方：セルによる降下から一般の Cat∞ 値分類を閉じる主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ元の区間 Hom 作用は、元の分類主写像の同じ後合成作用そのもの。 -/
lemma cocartesianStraighteningHomInterval_factor
    {C : Type u} [Category.{u} C] (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianStraighteningHomInterval p q = coherentHomComparison p q ≫
      pinchedHomToIntervalMappingSpace (coherentNerveVertex p) (coherentNerveVertex q) ≫
        intervalMappingPostOfEq (cocartesianStraighteningCoherentMap C)
          (coherentNerveVertex p) (coherentNerveVertex q)
          (cocartesianStraighteningCoherentMap_vertex p.val.hom)
          (cocartesianStraighteningCoherentMap_vertex q.val.hom) := by
  apply intervalMappingUncurry_injective
  symm
  rw [← Category.assoc, intervalMappingPostOfEq_uncurry,
    pinchedHomToIntervalMappingSpace_uncurry, cocartesianStraighteningHomInterval_uncurry]
  exact Category.assoc _ _ _

/-- 元の Hom の同じ区間作用の同値性から、同じ分類主写像の充満忠実性が従う。 -/
lemma cocartesianStraighteningCoherentMap_isFullyFaithful_of_originalHomInterval
    (C : Type u) [Category.{u} C]
    (h : ∀ p q : CocartesianFibrationCategory (nerve C),
      IsQCatEquivalence (cocartesianStraighteningHomInterval p q)) :
    IsFullyFaithful (cocartesianStraighteningCoherentMap C) := by
  intro x y
  obtain ⟨p, rfl⟩ := (coherentNerveVertexEquiv (CocartesianFibrationCategory (nerve C))).surjective x
  obtain ⟨q, rfl⟩ := (coherentNerveVertexEquiv (CocartesianFibrationCategory (nerve C))).surjective y
  apply IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply pinchedHomMap_isQCatEquivalence_of_intervalPost
    (cocartesianStraighteningCoherentMap C) (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianStraighteningCoherentMap_vertex p.val.hom)
    (cocartesianStraighteningCoherentMap_vertex q.val.hom)
  have hpq := h p q
  rw [cocartesianStraighteningHomInterval_factor] at hpq
  exact (coherentHomComparison_isQCatEquivalence p q).cancel_left hpq

end SerrePositivity.InfinityCategories
