module

public import SerrePositivity.KST.DerivedBlowup.ExteriorConeIso
public import SerrePositivity.KST.DerivedBlowup.ExteriorSequence

/-!
概要：KST Def3.1 の有限 Koszul 列を末尾の生成元で分解する。
方針：Fin.castSucc に沿う制限と末尾の評価を、添字の押し出しと単一生成元で逆にする。
規約：最後の関係式を外側の cone に取る既存 koszulComplex と同じ順序。
使われ方：有限列の外積模型と反復 cone 模型の帰納比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {n : ℕ}

/-- 概要：有限自由生成加群を先頭n個と末尾の係数へ分解する。
方針：castSucc への制限と last での評価を使う。
規約：KST Def3.1。使われ方：生成元分解同型の順写像。 -/
def sequenceGeneratorSplit : (Fin (n + 1) →₀ R) →ₗ[R] ((Fin n →₀ R) × R) :=
  (Finsupp.lcomapDomain Fin.castSucc (Fin.castSucc_injective n)).prod
    (Finsupp.lapply (Fin.last n))

/-- 概要：分解した有限自由生成加群を末尾の生成元とともに復元する。
方針：castSucc の押し出しに last の単一項を加える。
規約：KST Def3.1。使われ方：生成元分解同型の逆写像。 -/
def sequenceGeneratorJoin : ((Fin n →₀ R) × R) →ₗ[R] (Fin (n + 1) →₀ R) :=
  (Finsupp.lmapDomain R R Fin.castSucc).comp (LinearMap.fst R _ _) +
    (Finsupp.lsingle (Fin.last n)).comp (LinearMap.snd R _ _)

/-- 概要：末尾の添字は castSucc の像に入らない。
方針：Fin.castSucc_ne_last を使う。
規約：KST Def3.1。使われ方：生成元分解の末尾成分の計算。 -/
theorem sequenceLast_notMem_range :
    Fin.last n ∉ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

/-- 概要：有限列の自由生成加群の末尾分解は線形同型。
方針：castSucc と last の場合に分けて両側の逆元律を示す。
規約：KST Def3.1。使われ方：生成元追加の外積複体への同定。 -/
def sequenceGeneratorEquiv : (Fin (n + 1) →₀ R) ≃ₗ[R] ((Fin n →₀ R) × R) :=
  LinearEquiv.ofLinearMap sequenceGeneratorSplit sequenceGeneratorJoin (by
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · apply Finsupp.ext
      intro i
      simp [sequenceGeneratorSplit, sequenceGeneratorJoin, Finsupp.comapDomain_apply,
        Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n), Fin.castSucc_ne_last]
    · simp [sequenceGeneratorSplit, sequenceGeneratorJoin,
        Finsupp.mapDomain_of_notMem_range _ _ sequenceLast_notMem_range]) (by
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [sequenceGeneratorSplit, sequenceGeneratorJoin,
        Finsupp.mapDomain_of_notMem_range _ _ sequenceLast_notMem_range]
    · simp [sequenceGeneratorSplit, sequenceGeneratorJoin, Finsupp.comapDomain_apply,
        Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n), Fin.castSucc_ne_last])

/-- 概要：末尾分解の逆写像は Koszul 微分を保つ。
方針：線形結合と castSucc の押し出しの可換性を使う。
規約：KST Def3.1、先頭列と末尾関係式の順。
使われ方：外積生成元追加と有限列の比較の chain 条件。 -/
theorem sequenceGeneratorJoin_differential (x : Fin (n + 1) → R) :
    (Finsupp.linearCombination R x).comp (sequenceGeneratorEquiv (R := R)).symm.toLinearMap =
      exteriorProductDifferential (Finsupp.linearCombination R (Fin.init x)) (x (Fin.last n)) := by
  apply LinearMap.ext
  intro z
  change Finsupp.linearCombination R x
    (Finsupp.mapDomain Fin.castSucc z.1 + Finsupp.single (Fin.last n) z.2) = _
  rw [map_add, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_single]
  change Finsupp.linearCombination R (Fin.init x) z.1 + z.2 * x (Fin.last n) =
    Finsupp.linearCombination R (Fin.init x) z.1 + x (Fin.last n) * z.2
  rw [mul_comm z.2]

end SerrePositivity.KST.DerivedBlowup
