module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TruncatedConeSuccessor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierConeNextCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierZeroConeData

/-! # 有限次次数を持つ実分母図式の切断錐の延長

概要：共通分母による有限同時充填を退化正規化し、切断錐を一段延長する。
方針：全次次数単体を Fin で列挙し、一つの更新済み下次数錐へ全面を揃える。
規約：元の apex は追加分母で更新される。使われ方：有限次数の錐の存在帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)} {N : ℕ}

/-- 次次数の全単体が有限なら、実分母部分圏内の切断錐を一段延長できる。 -/
theorem dgVerdierTruncatedConeSuccessor_nonempty (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    [Finite (K _⦋N + 1⦌)] : Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (N + 1)) := by
  classical
  let := Fintype.ofFinite (K _⦋N + 1⦌)
  let e := Fintype.equivFin (K _⦋N + 1⦌)
  let τ : Fin (Fintype.card (K _⦋N + 1⦌)) → K _⦋N + 1⦌ := e.symm
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextFiniteRefinement_nonempty A D P x C τ
  let C' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextLower A D P x C τ T
  let U (σ : K _⦋N + 1⦌) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextSimplex A D P x C τ T (e σ)
  have hzero (σ : K _⦋N + 1⦌) :
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (U σ) = f.app _ σ := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextSimplex_face_zero A D P x C τ T (e σ)).trans
      (congrArg (f.app _) (e.symm_apply_apply σ))
  have hfirst (σ : K _⦋N + 1⦌) :
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).map
        (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op (U σ) = C'.apex :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextSimplex_first_vertex A D P x C τ T (e σ)
  have hpositive (σ : K _⦋N + 1⦌) (k : Fin (N + 2)) :
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ k.succ (U σ) =
        C'.simplex N le_rfl (K.δ k σ) := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextSimplex_face_positive A D P x C τ T (e σ) k).trans
      (congrArg (fun w => C'.simplex N le_rfl (K.δ k w)) (e.symm_apply_apply σ))
  exact ⟨C'.normalizedSuccessor U hzero hfirst hpositive⟩

/-- 各次数が有限な実分母図式は任意の有限次数まで実錐を持つ。 -/
theorem dgVerdierTruncatedConeData_nonempty (hfinite : ∀ n, Finite (K _⦋n⦌)) (N : ℕ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) := by
  induction N with
  | zero =>
    let := hfinite 0
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierZeroConeData_nonempty A D
  | succ N ih =>
    let := hfinite (N + 1)
    obtain ⟨C⟩ := ih
    exact dgVerdierTruncatedConeSuccessor_nonempty A D C

end SerrePositivity.InfinityCategories.Project.DerivedCategories
