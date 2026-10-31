module

public import SerrePositivity.CommutativeAlgebra.Perfection.Approximation
public import SerrePositivity.LengthAlgebra.Normalized

/-!
# Perfection の部分代数の近似による核の評価

完全閉包の中の近似 `perfectionApproximation`（CommutativeAlgebra/Perfection/Approximation）について、
共通分母を与えれば、商への写像の核の正規化長さを分母倍写像の余核の長さで評価できる。
定理2.5では `R = Λ` として `B_q` の像を扱う。テンソル積表示との同定は `PerfectBaseChange.lean`、
近似環の商の正規化長さは `PerfectApproximationLength.lean` で証明する。
共通分母の一般論は `TraceConductor.lean` にあり、正規な基底を仮定した塔への適用は
`PerfectConductor.lean` で証明済み。
-/

public section
universe u
namespace SerrePositivity.Section2

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (R : Type u) [CommRing R] [Algebra R (PerfectClosure D p)]

/-- 有限段の近似に対する、共通分母からの核の評価。
長さの有限性と共通分母の条件を明示的に受け取る。この二条件を定理2.5の設定で
得るためには、それぞれテンソル積表示とトレースの議論が別途必要である。 -/
theorem perfectionApproximation_kernel_bound {J : Ideal R} (lam : NormalizedLength R J)
    (n : ℕ) (I : Ideal (perfectionApproximation D p R n))
    (g : perfectionApproximation D p R n)
    (hg : ∀ c : PerfectClosure D p, (g : PerfectClosure D p) * c ∈
      perfectionApproximation D p R n)
    (htors : IsPowTorsion J ((perfectionApproximation D p R n) ⧸ I))
    (hfinite : lam.len ((perfectionApproximation D p R n) ⧸ I) ≠ ⊤) :
    lam.len (LinearMap.ker
      ((quotientToExtension (C := PerfectClosure D p) I).toLinearMap.restrictScalars R)) ≤
    lam.len ((perfectionApproximation D p R n) ⧸ (I ⊔ Ideal.span {g})) := by
  apply len_ker_quotientToExtension_le R lam Subtype.val_injective I g _ htors hfinite
  intro c
  exact ⟨⟨(g : PerfectClosure D p) * c, hg c⟩, rfl⟩

end SerrePositivity.Section2
