module
public import SerrePositivity.DifferentialGraded.Module.FreeSphereClosedCoproductSupport
public import SerrePositivity.DifferentialGraded.Presentation.FiniteRowCoefficientBound
/-!
概要：全整数シフトの自由 sphere の直和間の実閉射を、κ個以下の行有限係数から回収する。
方針：各自由 sphere の閉射の有限 support を選択し、余積の普遍性で元の全射を同定する。
規約：係数は自由 sphere 間の実閉射で、元の Hom 複体への係数抽出は別工程。
使われ方：c′ の全シフト自由直和における有限係数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleFreeSphereCoproduct_closed_matrix {I J : Type u}
    (x : I → D) (n : I → ℤ) (y : J → D) (m : J → ℤ)
    (f : (∐ fun i => freeSphere R D (x i) (n i)) ⟶ ∐ fun j => freeSphere R D (y j) (m j))
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    ∃ (support : I → Finset J)
      (coefficient : ∀ i j, freeSphere R D (x i) (n i) ⟶ freeSphere R D (y j) (m j)),
      (Sigma.desc (fun i => ∑ j ∈ support i,
        coefficient i j ≫ Sigma.ι (fun j => freeSphere R D (y j) (m j)) j) = f) ∧
      Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  choose support coefficient hrow using (fun i => moduleFreeSphereClosedCoproduct_rep
    R D (x i) (n i) (fun j => freeSphere R D (y j) (m j))
    (Sigma.ι (fun i => freeSphere R D (x i) (n i)) i ≫ f))
  refine ⟨support, coefficient, ?_, finiteRowCoefficientIndex_cardinal_le support κ hκ hI⟩
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc]
  exact hrow i

end SerrePositivity.DifferentialGraded
