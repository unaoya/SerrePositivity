module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRightSliceAppendCone
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DoubleRightPointFaces

/-!
概要：指定射を追加した実錐の前面と最終辺を、元の全錐と同じ指定射へ戻す。
方針：二重 join の包含を元の単体の実面へ移す。
規約：同じ全図式と固定辺を保持。使われ方：指定射上の実 slice 族。
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

/-- 同じ追加錐の前面は、元の全錐そのもの。 -/
lemma coherentRightSliceAppendCone_front {n : ℕ} (c : RZ _⦋n⦌) :
    joinInl (join (Δ[n] : SSet.{max u v}) Δ[0]) Δ[0] ≫ coherentRightSliceAppendCone g c =
      c.val := by
  rw [coherentRightSliceAppendCone, ← Category.assoc, doubleRightPointCoordinates_front,
    Category.assoc, SSet.yonedaEquiv_symm_naturality_left, PinchedHom.front_eq_δ]
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    ((SimplicialNerve C).δ (Fin.last (n + 2))
      (coherentSimplexAppendMorphism _ _)) = _
  rw [coherentSimplexAppendMorphism_face_last]
  simp only [coherentRightSliceSimplex, Equiv.symm_apply_apply,
    Iso.hom_inv_id_assoc]

/-- 同じ追加錐の最終辺は、元の指定射の辺に厳密に固定される。 -/
lemma coherentRightSliceAppendCone_tail {n : ℕ} (c : RZ _⦋n⦌) :
    joinMap (joinInr (Δ[n] : SSet.{max u v}) Δ[0]) (𝟙 Δ[0]) ≫
        coherentRightSliceAppendCone g c =
      (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (coherentNerveEdge g).edge := by
  rw [coherentRightSliceAppendCone, ← Category.assoc, doubleRightPointCoordinates_tail,
    Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  have h := coherentSimplexAppendMorphism_terminalEdge_of_eq
    (coherentRightSliceSimplex Z c) (coherentRightSliceSimplex_last Z c) g
  exact congrArg (fun s => (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm s) h

end SerrePositivity.InfinityCategories.F2
