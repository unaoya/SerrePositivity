module

public import SerrePositivity.CLMST.Almost
public import SerrePositivity.CLMST.PerfectoidIdealCompletedMul

/-! # mod p^N の perfectoid ideal の冪等性（証明済み互換入口）

元の主イデアル商の導来完備性と証明済みのperfectoid化の全射性から、
選択したperfectoid idealの核商のperfectoid性を得る。
その元の完備導来乗法の同型性を通じて、同じイデアルの全mod p冪像の冪等性を証明する。

対応する原典：CLMST arXiv:2209.04046v4, §2.4、およびBhatt–Scholze Remark 10.7。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs

/-- 元のperfectoid idealのmod p冪像は全指数で冪等。
gの非零性・根の選択・整域性・Noether性は要求しない。 -/
theorem perfectoidIdealMod_idempotent
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (N : ℕ) :
    perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N :=
  perfectoidIdeal_mod_power_idempotent R p hR g N

end SerrePositivity.CLMST.Inputs
