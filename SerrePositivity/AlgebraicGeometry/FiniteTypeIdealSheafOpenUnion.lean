module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafOpenCover

/-!
概要：開の和への制限の有限型性の判定。
方針：既存の iSupOpenCover に開被覆の判定を適用する。
規約：開族の有限性は不要。
使われ方：Stacks 01PF の有限被覆による帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u v

/-- 開の和への制限は、各開への制限が有限型なら有限型。 -/
theorem isFiniteTypeIdealSheaf_comap_iSup {X : Scheme.{u}}
    (K : X.IdealSheafData) {ι : Type v} (U : ι → X.Opens)
    (h : ∀ i, IsFiniteTypeIdealSheaf (K.comap (U i).ι)) :
    IsFiniteTypeIdealSheaf (K.comap (⨆ i, U i).ι) := by
  apply isFiniteTypeIdealSheaf_of_openCover _ (Scheme.Opens.iSupOpenCover U)
  intro i
  change IsFiniteTypeIdealSheaf
    ((K.comap (⨆ i, U i).ι).comap (X.homOfLE (le_iSup U i)))
  rw [← _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, X.homOfLE_ι]
  exact h i

end SerrePositivity.AlgebraicGeometry
