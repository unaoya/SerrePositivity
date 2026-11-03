module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceCoordinates

/-!
概要：元の coherent 右 slice の各全錐を、同じ指定射で後合成する。
方針：最後の対象だけを指定後合成し、標準 join へ戻す。
規約：元の全錐・指定射・全添字制限を保持。使われ方：元の合成 prism の終域自然性。
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

/-- 元の全錐の最後へ、同じ指定射を後合成した実際の右 slice 単体。 -/
def coherentRightSlicePostSimplex {n : ℕ} (c : RZ _⦋n⦌) : RW _⦋n⦌ := by
  let s := coherentRightSliceSimplex Z c
  let s' := coherentSimplexLastPost s (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g)
  refine ⟨(joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s', ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left]
  have hv : (SimplicialNerve C).map (PinchedHom.lastVertex n).op s' =
      coherentNerveVertex W := by
    apply (coherentNerveVertexEquiv C).symm.injective
    exact coherentSimplexLastPost_last s (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g)
  rw [hv]

/-- 同じ後合成錐の豊穣座標は、元の単体の指定後合成そのもの。 -/
lemma coherentRightSlicePostSimplex_coordinate {n : ℕ} (c : RZ _⦋n⦌) :
    coherentRightSliceSimplex W (coherentRightSlicePostSimplex g c) =
      coherentSimplexLastPost (coherentRightSliceSimplex Z c)
        (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g) := by
  simp only [coherentRightSliceSimplex, coherentRightSlicePostSimplex,
    Category.assoc, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 指定後合成は、元の実錐の面・退化を含む全添字制限に厳密に自然。 -/
lemma coherentRightSlicePostSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : RZ _⦋n⦌) :
    (RW).map α.op (coherentRightSlicePostSimplex g c) =
      coherentRightSlicePostSimplex g ((RZ).map α.op c) := by
  apply coherentRightSliceSimplex_injective W
  rw [coherentRightSliceSimplex_naturality, coherentRightSlicePostSimplex_coordinate,
    coherentRightSlicePostSimplex_coordinate, coherentSimplexLastPost_reindex]
  rw [← Category.assoc, eqToHom_trans]
  exact coherentSimplexLastPost_of_source_eq
    (coherentRightSliceSimplex_naturality Z α c).symm
    ((coherentSimplexLastReindex_last α (coherentRightSliceSimplex Z c)).trans
      (coherentRightSliceSimplex_last Z c))
    (coherentRightSliceSimplex_last Z ((RZ).map α.op c)) g

end SerrePositivity.InfinityCategories.F2
