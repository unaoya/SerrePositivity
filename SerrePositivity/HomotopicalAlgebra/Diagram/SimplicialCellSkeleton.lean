module
public import SerrePositivity.HomotopicalAlgebra.Diagram.SimplicialDiagramSkeleton

/-!
概要：非退化単体の境界は、元の直前の骨格をちょうど引き戻す。
方針：空の部分複体からの既存の相対細胞分解を同じ単体に適用する。
規約：IS-W2 R03aの骨格の貼り合わせの証明分割。
使われ方：自由なBK細胞の境界射と旧骨格との厳密な照合。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory SSet
open scoped Simplicial

/-- 非退化単体による旧骨格の逆像は、元の標準境界そのもの。 -/
theorem nondegenerate_preimage_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    (X.skeleton n).preimage (yonedaEquiv.symm c.val) = ∂Δ[n] := by
  let i := (⊥ : X.Subcomplex).ι
  let d : relativeCellComplexOfMono.Cell i n :=
    { simplex := c.val
      nonDegenerate := c.property
      notMem := by
        rintro ⟨x, hx⟩
        exact x.property }
  have h := d.preimage_map
  simpa [skeletonOfMono, i] using h

/-- 同じ非退化単体の全標準単体は、新しい骨格へ入る。 -/
theorem nondegenerate_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (yonedaEquiv.symm c.val) ≤ X.skeleton (n+1) := by
  rw [Subcomplex.range_eq_ofSimplex]
  simpa only [Equiv.apply_symm_apply] using
    X.ofSimplex_le_skeleton c.val (Nat.lt_succ_self n)

/-- 同じ境界からの写像は旧骨格へ入る。 -/
theorem nondegenerate_boundary_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (∂Δ[n].ι ≫ yonedaEquiv.symm c.val) ≤ X.skeleton n := by
  rw [Subcomplex.range_comp, Subcomplex.image_le_iff, nondegenerate_preimage_skeleton]
  simp

end SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
