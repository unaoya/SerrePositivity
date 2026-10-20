module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralRefinedCochains
public import SerrePositivity.InfinityCategories.Derived.DGGradedCompositionDegreeTransport

/-! # 追加分母後の一般 A 微分式を元の次数へ戻す

概要：原始元からの A 微分を、元の最上位方程式と同じ −n−1+1 の次数で読む。
方針：正規化の線形同型の単射性と、閉前合成・零次数後合成の輸送を使う。
規約：R・K と追加実閉射は同じもの。使われ方：細分ホーンの二未知解への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D] {n : ℕ}
variable {P : Set D} {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D}
variable (H : DGGeneralLastHornResidualRefinement P σ)

/-- 同じ実 A の微分式を、元の K と同じ未正規化次数で回収する。 -/
lemma DGGeneralLastHornResidualRefinement.a_differential_original :
    differential A H.a =
      dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (dgGeneralLastHornTopResidual σ) H.s +
        compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
          (dgLastHornPenultimate_lt_last n)) H.Q (by omega) := by
  apply (gradedHomTransport (A := A) (D := D) (rfl : H.q = H.q) rfl
    (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))).injective
  rw [dgGradedHomTransport_differential_to, map_add, dgGradedPrecompose_degreeTransport,
    dgZeroPostcompose_outputTransport]
  exact H.a_differential

end SerrePositivity.InfinityCategories
