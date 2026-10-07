module

public import SerrePositivity.Descent.Lemma34
public import SerrePositivity.GeometricFiber
public import SerrePositivity.Perfect

/-!
# Lemma 3.5（通常ノルム比較、論文 §3.4）

`Setup34` の設定に加えて、有限群 `G` が `A` 上 `T` に作用し、`Spec T → Spec A` の
幾何ファイバーで推移的とする。`P` が閉点 `V(m_A T)` に台をもつ完全 `T` 複体なら、
通常評価 `χ_T` と `λ` 評価 `χ_C` はどちらも有限で、ノルム和の上で一致する（(3.11)）：

  `Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)`

論文の「`K_0^{m_A}(A)` の像と `G` 不変な有理類の上でも一致する」という一般形は、
Lemma 3.5 自身の証明で Theorem 3.1 を使う部分なので、Lean の主張には入れない。
証明は Theorem 3.1（`H = A`、`K₀ ⊗ ℚ` のレベル）と Lemma 3.4、Koszul 分裂 (3.12)、
hyper-Tor スペクトル系列による。Theorem 3.1 を入力束 `Inputs.Descent` として置いてから証明する。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- **Lemma 3.5**（通常ノルム比較）。 -/
theorem lemma_3_5 (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    (p : ℕ) {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (_S : Setup34 A T C p z lam)
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
    (_hG : IsGeometricallyTransitive A T G)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (_hP : IsPerfectSupported ((maximalIdeal A).map (algebraMap A T)) P) :
    (∀ (g : G) (i : ℤ), Module.length T ((twist g P).homology i) ≠ ⊤) ∧
      (∀ (g : G) (i : ℤ), lam.len ((baseChange (algebraMap T C) (twist g P)).homology i) ≠ ⊤) ∧
      ∑ g : G, chiOrd (twist g P) = ∑ g : G, chiLam lam (algebraMap T C) (twist g P) := by
  sorry

end SerrePositivity
