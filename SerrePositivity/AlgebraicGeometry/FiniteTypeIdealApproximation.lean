module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSectionExtension

/-!
概要：有限アフィン族上の有限個の切断を含む有限型部分イデアル層を選ぶ。
方針：各開の有限集合の延長の有限和を取る。
規約：Stacks 01PF・01PG のイデアル層の場合。基底は qcqs。
使われ方：C02.(i)、有限表示閉包絡を作るための有限型近似。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- qcqs 基底の有限個のアフィン開の切断を、有限型部分イデアル層に同時に含める。 -/
theorem exists_finiteType_subideal_containing_affine_sections
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) {ι : Type u} [Finite ι] (U : ι → X.affineOpens)
    (s : ∀ i, Finset Γ(X, (U i).1)) (hs : ∀ i x, x ∈ s i → x ∈ K.ideal (U i)) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      ∀ i x, x ∈ s i → x ∈ J.ideal (U i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose J hJK hJ hmem using fun i ↦
    exists_finiteType_subideal_containing_affine_finset K (U i) (s i) (hs i)
  have hfiniteSup : ∀ t : Finset ι, IsFiniteTypeIdealSheaf (t.sup J) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro V; exact Submodule.fg_bot
    | insert i t hi ih => rw [Finset.sup_insert]; exact (hJ i).sup ih
  refine ⟨Finset.univ.sup J, Finset.sup_le (fun i _ ↦ hJK i), hfiniteSup _, ?_⟩
  intro i x hx
  have hle : J i ≤ Finset.univ.sup J := Finset.le_sup (Finset.mem_univ i)
  exact hle (U i) (hmem i x hx)

end SerrePositivity.AlgebraicGeometry
