module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Defs
/-!
概要：固定自由加群の商からの線形写像の像が指定 submodule に入ることを基底で判定する。
方針：商への全射で元を持ち上げ、有限支持線形結合の帰納を使う。
規約：関係部分加群の生成元数を制限しない。
使われ方：c′ の元の出発 Hom 提示の全像を κ 個の係数で係数閉包に含める。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
variable {R B : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

lemma quotientGeneratorImage_mem (P : Submodule R (B →₀ R))
    (L : ((B →₀ R) ⧸ P) →ₗ[R] M) (S : Submodule R M)
    (h : ∀ b, L (P.mkQ (Finsupp.single b 1)) ∈ S) (x : (B →₀ R) ⧸ P) : L x ∈ S := by
  obtain ⟨v, rfl⟩ := P.mkQ_surjective x
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
  | single b r =>
    have hs : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    rw [hs, map_smul, map_smul]
    exact S.smul_mem r (h b)

end SerrePositivity.DifferentialGraded
