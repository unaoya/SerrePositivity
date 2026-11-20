module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.RegularMinorPureTransformEquiv
public import SerrePositivity.AlgebraicGeometry.LocalMinorPureTransformGeneration
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
概要：KST §5、Stacks 0810・080Z の正則単項小行列式による純変換の自由性。
方針：実際のピボットと随伴行列の係数の商を選び、補成分との実同型を構成する。
規約：有限自由表示と元の境界の純変換を固定する。
使われ方：係数中心の blowup 後の特別な局所環で純変換の自由性を判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則単項小行列式と次次数の消滅から純変換と補成分の実同型が存在する。
方針：単元倍のピボットと随伴行列の割り算を実際に選び、正則ピボットの同型を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2・080Z, Lemma 15.8.9、局所環上の文言。
使われ方：選択した正規化データを仮定として残さない純変換の自由性判定。
-/
theorem exists_boundaryPureTransform_complement_equiv_of_regular_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Finite m]
    (H : Matrix m n R) (k : ℕ) (d f : R) (hd : IsRegular d) (hf : IsRegular f)
    (N : ℕ) (hdf : d ∣ f ^ N) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hI : matrixMinorIdeal H k = Ideal.span {d}) (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    ∃ r : Fin k → m, Function.Injective r ∧
      Nonempty (({i : m // i ∉ Set.range r} → R) ≃ₗ[R] modulePureTransform f M) := by
  classical
  obtain ⟨r, c, u, hr, _, hdet⟩ := exists_injective_minor_unit_multiple H k d hd hI
  let A := H.submatrix r c
  let B := H.submatrix (Subtype.val : {i : m // i ∉ Set.range r} → m) c
  have hdiv : ∀ i j, d ∣ (A.updateRow j (B i)).det := by
    intro i j
    apply Ideal.mem_span_singleton.mp
    rw [← hI]
    let r' : Fin k → m := Function.update r j i.val
    have hmat : H.submatrix r' c = A.updateRow j (B i) := by
      ext l t
      change H (r' l) (c t) = Function.update A j (B i) l t
      by_cases hl : l = j
      · subst l
        rw [Function.update_self]
        have hr' : r' j = i.val := Function.update_self _ _ _
        rw [hr']
        rfl
      · rw [Function.update_of_ne hl]
        have hr' : r' l = r l := Function.update_of_ne hl _ _
        rw [hr']
        rfl
    rw [← hmat]
    exact det_submatrix_mem_matrixMinorIdeal H k r' c
  choose C hC using hdiv
  have hBC : B * A.adjugate = d • (C : Matrix {i : m // i ∉ Set.range r} (Fin k) R) := by
    ext i j
    rw [mul_adjugate_entry_eq_updateRow_det, hC i j]
    rfl
  exact ⟨r, hr, ⟨regularMinorBoundaryPresentationComplementEquiv H r hr c q hq hH
    d f hd hf N hdf u hdet C hBC hzero⟩⟩

/--
概要：正則単項の k 次小行列式と次次数の消滅の下で純変換は階数 N-k の自由加群。
方針：ピボット外の自由成分との実同型と、行の分解による濃度の等式を使う。
規約：KST §5、Stacks 0810・080Z、N は元の生成元の個数。
使われ方：係数 blowup 後の純変換の自由性と階数を同時に得る。
-/
theorem boundaryPureTransform_free_and_finrank_of_regular_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Fintype m]
    (H : Matrix m n R) (k : ℕ) (d f : R) (hd : IsRegular d) (hf : IsRegular f)
    (N : ℕ) (hdf : d ∣ f ^ N) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hI : matrixMinorIdeal H k = Ideal.span {d}) (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    Module.Free R (modulePureTransform f M) ∧
      Module.finrank R (modulePureTransform f M) = Fintype.card m - k := by
  classical
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_boundaryPureTransform_complement_equiv_of_regular_minorIdeal
    H k d f hd hf N hdf q hq hH hI hzero
  let K := {i : m // i ∉ Set.range r}
  let : Fintype K := Fintype.ofFinite K
  refine ⟨Module.Free.of_equiv e, ?_⟩
  have hcard : k + Fintype.card K = Fintype.card m := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (rowPartitionEquiv r hr)
  have he : Fintype.card K = Module.finrank R (modulePureTransform f M) := by
    have he₀ : Module.finrank R (K → R) = Module.finrank R (modulePureTransform f M) := e.finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card] at he₀
  omega

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
