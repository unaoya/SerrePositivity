module
public import SerrePositivity.DifferentialGraded.Module.RepresentableClosedCoproductSupport
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.YonedaClosedPreimage
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.CoefficientClosure
/-!
概要：代表加群の直和間の実閉射を、κ個以下の元の閉射からなる行有限行列で表示する。
方針：各包含からの閉射を有限 support へ分解し、Yoneda の全 Hom 同型で係数を戻す。
規約：各行の閉射等式を保持し、列数や係数環の基数は制限しない。
使われ方：c′ の自由直和閉射の係数精密化。シフトと一般 cell の場合は別工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleRepresentableCoproduct_closed_matrix {I J : Type u}
    (x : I → D) (y : J → D)
    (f : (∐ fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) ⟶
      ∐ fun j => ForgetEnrichment.of (Complex R) (representable R (y j)))
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    ∃ (support : I → Finset J)
      (coefficient : ∀ i j, ForgetEnrichment.of (Complex R) (x i) ⟶
        ForgetEnrichment.of (Complex R) (y j)),
      (∀ i, ∑ j ∈ support i, (dgYoneda R D).onClosed.map (coefficient i j) ≫
        Sigma.ι (fun j => ForgetEnrichment.of (Complex R) (representable R (y j))) j =
        Sigma.ι (fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) i ≫ f) ∧
      Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  choose support row hrow using (fun i => moduleRepresentableClosedCoproduct_rep R D (x i)
    (fun j => ForgetEnrichment.of (Complex R) (representable R (y j)))
    (Sigma.ι (fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) i ≫ f))
  let coefficient := fun i j => dgYonedaClosedPreimage R D (row i j)
  refine ⟨support, coefficient, ?_, finiteRowCoefficientIndex_cardinal_le support κ hκ hI⟩
  intro i
  simpa only [coefficient, dgYonedaClosedPreimage_map] using hrow i

end SerrePositivity.DifferentialGraded
