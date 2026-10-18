module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：整数次数の恒等微分を持つ二項複体と、その非輪状性。
方針：二つの非零次数では微分の同型性、その他では項の零性から完全性を示す。
規約：任意のアーベル圏。次数の有界性に関する仮定を他の複体へ課さない。
使われ方：Stacks 19.12.5・19.12.6、TT §3・§8、Toën §3.2 の各項 injectivity の試験。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]

/--
概要：n と n+1 に同じ対象を置き恒等微分で結ぶ二項複体。
方針：Mathlib の実際の double を用いる。
規約：整数次数。
使われ方：Stacks 19.12.6、TT §3 の各項 injectivity の試験対象。
-/
def cochainDisk (X : C) (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.double (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

/--
概要：恒等微分の二項複体は非輪状。
方針：非零の微分が同型であることと、残りの項の零性から示す。
規約：全整数次数での完全性。
使われ方：Stacks 19.12.6、TT §3 の単射準同型の試験族。
-/
lemma cochainDisk_acyclic (X : C) (n : ℤ) : (cochainDisk X n).Acyclic := by
  have hn : n ≠ n + 1 := by omega
  have hd : IsIso ((cochainDisk X n).d n (n + 1)) := by
    dsimp [cochainDisk]
    rw [HomologicalComplex.double_d _ _ hn]
    infer_instance
  intro k
  rw [HomologicalComplex.exactAt_iff' (cochainDisk X n) (k - 1) k (k + 1) (by simp) (by simp)]
  by_cases h : k = n
  · subst k
    apply (ShortComplex.exact_iff_mono _ ?_).mpr
    · change Mono ((cochainDisk X n).d n (n + 1)); infer_instance
    · change (cochainDisk X n).d (n - 1) n = 0
      exact HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)
  · by_cases h' : k = n + 1
    · subst k
      apply (ShortComplex.exact_iff_epi _ ?_).mpr
      · change Epi ((cochainDisk X n).d (n + 1 - 1) (n + 1))
        rw [show n + 1 - 1 = n by omega]
        infer_instance
      · change (cochainDisk X n).d (n + 1) (n + 1 + 1) = 0
        exact HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)
    · exact ShortComplex.exact_of_isZero_X₂ _
        (HomologicalComplex.isZero_double_X (𝟙 X)
          (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) k h h')

end SerrePositivity.KST.DerivedGeometry
