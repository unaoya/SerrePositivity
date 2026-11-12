module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionPrism
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostReindex

/-!
概要：coherent 右 slice の全錐単体を、同じ最後の対象を持つ豊穣単体で読む。
方針：標準 join 同型と Yoneda を使い、元の全射を厳密に回収する。
規約：全単体・全添字制限を保持。使われ方：元の右 slice の指定終域後合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (Z : C)
local notation "R" => sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))

/-- 元の右 slice の錐単体を同じ最後の頂点を持つ豊穣単体へ移す。 -/
def coherentRightSliceSimplex {n : ℕ} (c : R _⦋n⦌) : (SimplicialNerve C) _⦋n + 1⦌ :=
  SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫ c.val)

/-- 標準 join と Yoneda による座標は、元の実錐の全射を忠実に保持する。 -/
lemma coherentRightSliceSimplex_injective {n : ℕ} :
    Function.Injective (coherentRightSliceSimplex Z (n := n)) := by
  intro c d h
  apply Subtype.ext
  apply (cancel_epi (joinStdSimplexIso n 0).inv).1
  exact SSet.yonedaEquiv.injective h

/-- 元の錐単体の最後の対象は、指定されていた同じ右 slice の頂点。 -/
lemma coherentRightSliceSimplex_last {n : ℕ} (c : R _⦋n⦌) :
    (coherentRightSliceSimplex Z c).obj ⟨ULift.up (Fin.last (n + 1))⟩ = Z := by
  have hi : stdSimplex.map (PinchedHom.lastVertex n) ≫ (joinStdSimplexIso n 0).inv =
      joinInr (Δ[n] : SSet.{max u v}) Δ[0] := by
    rw [← joinStdSimplexIso_rightPoint_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hv : (SimplicialNerve C).map (PinchedHom.lastVertex n).op
      (coherentRightSliceSimplex Z c) = coherentNerveVertex Z := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_naturality_left]
    simp only [coherentRightSliceSimplex, Equiv.symm_apply_apply]
    rw [← Category.assoc, hi, c.property]
  exact congrArg (coherentNerveObject (C := C)) hv

/-- 元の錐単体の前面は、同じ右 slice の元の射影の値そのもの。 -/
lemma coherentRightSliceSimplex_front {n : ℕ} (c : R _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentRightSliceSimplex Z c) =
      (sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex Z))).app
        (Opposite.op ⦋n⦌) c := by
  have hi : stdSimplex.map (PinchedHom.front n) ≫ (joinStdSimplexIso n 0).inv =
      joinInl (Δ[n] : SSet.{max u v}) Δ[0] := by
    rw [← joinStdSimplexIso_rightPoint_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  change stdSimplex.map (PinchedHom.front n) ≫
    SSet.yonedaEquiv.symm (coherentRightSliceSimplex Z c) =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (joinInl Δ[n] Δ[0] ≫ c.val))
  simp only [coherentRightSliceSimplex, Equiv.symm_apply_apply]
  rw [← Category.assoc, hi]

/-- 元の実錐の全添字制限は、同じ最後を固定する豊穣単体の制限そのもの。 -/
lemma coherentRightSliceSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (c : R _⦋n⦌) :
    coherentRightSliceSimplex Z ((R).map α.op c) =
      (SimplicialNerve C).map (PinchedHom.extend α).op (coherentRightSliceSimplex Z c) := by
  have hi : (joinStdSimplexIso m 0).inv ≫
      joinMap (stdSimplex.map α) (𝟙 (Δ[0] : SSet.{max u v})) =
      stdSimplex.map (PinchedHom.extend α) ≫ (joinStdSimplexIso n 0).inv := by
    have h := congrArg (fun k => (joinStdSimplexIso m 0).inv ≫ k ≫
      (joinStdSimplexIso n 0).inv) (joinStdSimplexIso_rightPoint_naturality α)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  simp only [coherentRightSliceSimplex, Equiv.symm_apply_apply]
  change (joinStdSimplexIso m 0).inv ≫ (joinMap (stdSimplex.map α) (𝟙 Δ[0]) ≫ c.val) = _
  rw [← Category.assoc, hi, Category.assoc]

end SerrePositivity.InfinityCategories.F2
