module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.SphericalBoundaryAlternating
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：球面的境界のホモトピー類の交代和は零である。
方針：Kan ホーンによる一面の消去を反復し、最後の隣接二面を比較する。
規約：面の実際の次数は二以上。
使われ方：Goerss–Jardine I §7、VIII §1、Kerodon §3.2.3。幾何的微分の符号関係。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SphericalBoundary
end SerrePositivity.KST.Spectra.SphericalBoundary
namespace SerrePositivity.InfinityCategories.Kan.SphericalBoundary
open SerrePositivity.KST.Spectra.SphericalBoundary

noncomputable section

variable {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}
  {a : Fin (n + 4) → X.PtSimplex (n + 2) x}

/-- 概要：最後の二面だけが残る球面的境界の交代和は零。
方針：元の単体を RelStruct と読み、隣接二面の同じ類を逆符号で消す。
規約：零から n + 1 の面は全て定数。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。境界簡約の終端。 -/
theorem alternatingClass_eq_zero_last (T : SphericalBoundary a)
    (hlower : ∀ j, j.val < n + 2 → a j = .const) : alternatingClass a = 0 := by
  let h : PtSimplex.RelStruct (a (Fin.last (n + 2)).castSucc)
      (a (Fin.last (n + 2)).succ) (Fin.last (n + 2)) :=
    { map := T.map
      δ_castSucc_map := T.face_eq _
      δ_succ_map := T.face_eq _
      δ_map_of_lt j hj := by
        rw [T.face_eq, hlower j
          (by simpa only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] using hj)]
        rfl
      δ_map_of_gt j hj := by exact (not_lt_of_ge (Fin.le_last j) hj).elim }
  have he : additiveClass (a (Fin.last (n + 2)).castSucc) =
      additiveClass (a (Fin.last (n + 2)).succ) :=
    congrArg Additive.ofMul (KanHomotopyGroup.sound h)
  unfold alternatingClass
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.castSucc.castSucc.val •
      additiveClass (a j.castSucc.castSucc)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hlower _ (by exact j.isLt), additiveClass_const, smul_zero]
  rw [hz, zero_add]
  change (-1 : ℤ) ^ (n + 2) • additiveClass (a (Fin.last (n + 2)).castSucc) +
    (-1 : ℤ) ^ (n + 3) • additiveClass (a (Fin.last (n + 2)).succ) = 0
  have hp : (-1 : ℤ) ^ (n + 3) = -((-1 : ℤ) ^ (n + 2)) := by
    rw [pow_succ, mul_neg_one]
  rw [he, hp, neg_smul, add_neg_cancel]

/-- 概要：既に定数である先頭部分から始めて、境界の交代和を消す。
方針：残りの面の数で帰納し、逆元と左因子の Kan 充填による簡約を使う。
規約：q + fuel は n + 2。最後の二面は帰納の終端で扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。一般の境界関係の証明。 -/
theorem alternatingClass_eq_zero_of_lower (fuel q : ℕ) (hq : q + fuel = n + 2)
    (T : SphericalBoundary a) (hlower : ∀ j, j.val < q → a j = .const) :
    alternatingClass a = 0 := by
  induction fuel generalizing q a with
  | zero =>
    apply alternatingClass_eq_zero_last T
    intro j hj
    exact hlower j (by omega)
  | succ fuel ih =>
    let p : Fin (n + 2) := ⟨q, by omega⟩
    obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse (a p.castSucc.castSucc) p
    obtain ⟨b, ⟨hb⟩⟩ := exists_left_factor ia (a p.succ.succ) p
    have hl : ∀ j, j.val < p.val → a j = .const := hlower
    rw [← alternatingClass_reduce hi hb hl]
    apply ih (q + 1) (by omega) (SphericalBoundaryReduction.reduce hi hb T hl)
    intro j hj
    exact ite_eq_left (show j.val ≤ p.val from by dsimp [p]; omega)

/-- 概要：球面的な境界のホモトピー類の交代和は零。
方針：空の定数部分から開始し、全ての先頭面を Kan 充填で消す。
規約：任意の Kan 複体と、二以上の次数の境界定数な面。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の幾何的微分の交代式。 -/
theorem alternatingClass_eq_zero (T : SphericalBoundary a) : alternatingClass a = 0 :=
  alternatingClass_eq_zero_of_lower (n + 2) 0 (Nat.zero_add _) T
    (fun j hj ↦ (Nat.not_lt_zero j.val hj).elim)

end

end SerrePositivity.InfinityCategories.Kan.SphericalBoundary

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.alternatingClass_eq_zero := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.alternatingClass_eq_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.alternatingClass_eq_zero_last := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.alternatingClass_eq_zero_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.alternatingClass_eq_zero_of_lower := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.alternatingClass_eq_zero_of_lower
