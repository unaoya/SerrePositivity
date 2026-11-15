module

public import SerrePositivity.AlgebraicGeometry.AffineFiniteTypeSubideal

/-!
概要：アフィン基底の有限個のアフィン開で元のイデアル層と一致する有限型部分を選ぶ。
方針：有限生成元の有限選択の補題に、各切断イデアルの生成元を渡す。
規約：有限型性は指定した開上でだけ仮定する。
使われ方：Stacks 01PF、開の重なりへの有限型部分イデアルの延長。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- アフィン基底上で、指定した有限族のアフィン開における一致を保つ有限型部分を選ぶ。 -/
theorem exists_finiteType_subideal_eq_on_affine_family_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (K : X.IdealSheafData)
    {ι : Type u} [Finite ι] (U : ι → X.affineOpens)
    (hK : ∀ i, (K.ideal (U i)).FG) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      ∀ i, J.ideal (U i) = K.ideal (U i) := by
  classical
  choose s hs using hK
  have hmem : ∀ i x, x ∈ s i → x ∈ K.ideal (U i) := by
    intro i x hx
    rw [← hs i]
    exact Ideal.subset_span hx
  obtain ⟨J, hJK, hJ, hcontains⟩ :=
    exists_finiteType_subideal_containing_affine_sections_of_isAffine K U s hmem
  refine ⟨J, hJK, hJ, fun i ↦ le_antisymm (hJK (U i)) ?_⟩
  rw [← hs i]
  exact Ideal.span_le.mpr (fun x hx ↦ hcontains i x hx)

end SerrePositivity.AlgebraicGeometry
