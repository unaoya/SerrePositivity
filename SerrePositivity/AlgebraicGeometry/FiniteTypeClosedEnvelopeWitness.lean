module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationClosedEnvelope

/-!
概要：C02 の閉包絡の構成で選んだイデアル層の有限型性を保持する。
方針：同じ有限個の切断を含む部分イデアルの構成から有限型性の証人も返す。
規約：既存の C02 の構成の性質の取り出し。旧宣言の名前と型は変えない。
使われ方：A07 の閉包絡に C03 の有限段の模型を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u

/-- C02 の閉包絡を作る同じ構成で、イデアル層の有限型性の証人を保持する。 -/
theorem exists_finiteType_closedEnvelope
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) (V : X.Opens) (hKV : (K.support : Set X) ⊆ V) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      (J.support : Set X) ⊆ V := by
  classical
  obtain ⟨t, ht⟩ := exists_finite_affine_sections_support_subset K V hKV
  let U (a : t) : X.affineOpens := a.1.1
  let s (a : t) : Finset Γ(X, (U a).1) := {(a.1.2 : Γ(X, (U a).1))}
  have hs : ∀ a x, x ∈ s a → x ∈ K.ideal (U a) := by
    intro a x hx
    rcases Finset.mem_singleton.mp (show x ∈ {(a.1.2 : Γ(X, (U a).1))} from hx) with rfl
    exact a.1.2.2
  obtain ⟨J, hJK, hJ, hcontains⟩ :=
    exists_finiteType_subideal_containing_affine_sections K U s hs
  refine ⟨J, hJK, hJ, ht J ?_⟩
  intro a ha
  exact hcontains ⟨a, ha⟩ a.2 (by simp [s])

end SerrePositivity.AlgebraicGeometry
