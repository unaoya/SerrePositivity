module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentAppendTerminalEdge
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DoubleRightPointCoordinates

/-!
概要：元の右 slice の全錐へ同じ指定射を付け足し、二つの終点を持つ実錐へ移す。
方針：元の全単体の追加を二重の標準 join 座標へ戻す。
規約：面・退化を含む全添字制限を保持。使われ方：元の三射の同時高次族。
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

/-- 元の実全錐へ指定射を追加した、二つの終点を持つ同じ実図式。 -/
def coherentRightSliceAppendCone {n : ℕ} (c : RZ _⦋n⦌) :
    join (join (Δ[n] : SSet.{max u v}) Δ[0]) Δ[0] ⟶ SimplicialNerve C :=
  doubleRightPointCoordinates n ≫ SSet.yonedaEquiv.symm
    (coherentSimplexAppendMorphism (coherentRightSliceSimplex Z c)
      (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g))

/-- 元の全錐への指定射の追加は、実二重 join 上でも全添字制限に自然。 -/
lemma coherentRightSliceAppendCone_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (c : RZ _⦋n⦌) :
    joinMap (joinMap (stdSimplex.map α) (𝟙 (Δ[0] : SSet.{max u v}))) (𝟙 Δ[0]) ≫
        coherentRightSliceAppendCone g c =
      coherentRightSliceAppendCone g ((RZ).map α.op c) := by
  unfold coherentRightSliceAppendCone
  rw [← Category.assoc, doubleRightPointCoordinates_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left, coherentSimplexAppendMorphism_reindex]
  have h := coherentSimplexAppendMorphism_of_source_eq
    (coherentRightSliceSimplex_naturality Z α c).symm
    ((coherentSimplexLastReindex_last α (coherentRightSliceSimplex Z c)).trans
      (coherentRightSliceSimplex_last Z c))
    (coherentRightSliceSimplex_last Z ((RZ).map α.op c)) g
  simpa only [← Category.assoc, eqToHom_trans] using
    congrArg (fun s => doubleRightPointCoordinates m ≫ SSet.yonedaEquiv.symm s) h

end SerrePositivity.InfinityCategories.F2
