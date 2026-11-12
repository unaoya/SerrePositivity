module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectivePieces
public import Mathlib.RingTheory.Ideal.Operations

/-!
概要：イデアル倍の斉次成分を、元の斉次成分のイデアル倍として取り出す。
方針：次数成分への線形射影と、イデアル倍の生成元による帰納を使う。
規約：商への底変換に flat を仮定しない。
使われ方：I 進閉厚化の標準開の実際の係数と Rees の商表示の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open SerrePositivity.HilbertSerre
universe u
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- イデアル倍の元を次数 d に射影すると、次数 d の成分のイデアル倍に入る。 -/
theorem projectiveIdealGradeProjection_mem (d : ℕ) {m : M}
    (hm : m ∈ I • (⊤ : Submodule R M)) : gradeProjection G d m ∈ I • G d := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr x hx
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (DirectSum.decompose G x d).property
  · intro x y hx hy
    rw [map_add]
    exact (I • G d).add_mem hx hy

/-- 斉次元が全体のイデアル倍に入ることと、同じ次数成分のイデアル倍に入ることは同値。 -/
theorem projectiveHomogeneous_mem_ideal_smul_iff (d : ℕ) {m : M} (hm : m ∈ G d) :
    m ∈ I • (⊤ : Submodule R M) ↔ m ∈ I • G d := by
  constructor
  · intro h
    simpa only [gradeProjection_same G d hm] using projectiveIdealGradeProjection_mem I G d h
  · intro h
    exact (Submodule.smul_mono (show I ≤ I from le_rfl)
      (show G d ≤ (⊤ : Submodule R M) from le_top)) h

variable {ι : Type} [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]

/-- 拡大イデアルで書いた Rees の部分加群は、元の Iⁿ 倍の部分加群そのもの。 -/
theorem reesAdicProjectiveSubmodule_eq_ideal_smul (n : ℕ) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I n = I ^ n • (⊤ : Submodule R M) := by
  unfold reesAdicProjectiveSubmodule
  rw [reesExtendedAdic_restrictScalars]

end SerrePositivity.AlgebraicGeometry
