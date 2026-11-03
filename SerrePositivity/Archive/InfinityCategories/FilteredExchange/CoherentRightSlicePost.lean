module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSlicePostSimplex

/-!
概要：指定射による coherent 右 slice の後合成を、元の底を厳密に保つ実写像にする。
方針：全錐の指定後合成を面・退化の自然性で束ね、同じ前面を回収する。
規約：元の全錐・底・指定射を保持。使われ方：元の合成 prism の終域自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C} (g : Z ⟶ W)
local notation "RZ" => sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))
local notation "RW" => sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex W))

/-- 元の同じ全右 slice の各錐へ指定射を後合成する実際の単体集合写像。 -/
def coherentRightSlicePost : RZ ⟶ RW where
  app _ := ↾fun c => coherentRightSlicePostSimplex g c
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro c
    exact (coherentRightSlicePostSimplex_naturality g α.unop c).symm

/-- 指定後合成の実写像は、元の右 slice の射影を厳密に保つ。 -/
lemma coherentRightSlicePost_projection :
    coherentRightSlicePost g ≫ sliceOverProjection
        (SSet.yonedaEquiv.symm (coherentNerveVertex W)) =
      sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex Z)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  change (sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex W))).app
    (Opposite.op ⦋n⦌) (coherentRightSlicePostSimplex g c) = _
  rw [← coherentRightSliceSimplex_front W (coherentRightSlicePostSimplex g c),
    coherentRightSlicePostSimplex_coordinate]
  have he : (SimplicialNerve C).map (PinchedHom.front n).op
      (coherentSimplexLastPost (coherentRightSliceSimplex Z c)
        (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g)) =
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentRightSliceSimplex Z c) :=
      coherentSimplexLastPost_old_face _ _
  rw [he, coherentRightSliceSimplex_front]

end SerrePositivity.InfinityCategories.F2
