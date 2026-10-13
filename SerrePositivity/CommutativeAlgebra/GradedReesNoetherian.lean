module

public import SerrePositivity.CommutativeAlgebra.ReesPresentation

/-! # 商のNoether性から随伴次数環のNoether性へ

有限生成イデアルIの随伴次数環は(R/I)係数の有限変数多項式環の商。
MathlibのRees代数の有限型性と基底変換による定理を再利用する。
元の環RのNoether性は仮定しない。完備性によるRへの持ち上げは別の課題。
-/

public section
universe u
namespace SerrePositivity.HilbertSamuel
variable (R : Type u) [CommRing R] (I : Ideal R)

/-- 有限生成イデアルの随伴次数環は、係数商がNoetherならNoether。 -/
theorem isNoetherianRing_gradedReesRing_of_fg
    (hI : I.FG) [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (GradedReesRing R I) := by
  exact isNoetherianRing_reesAlgebra_quotient hI

/-- 有限生成な極大イデアルを持つ局所環の随伴次数環はNoether。
元の局所環のNoether性や完備性は仮定しない。 -/
theorem isNoetherianRing_gradedReesRing_of_maximalIdeal_fg
    [IsLocalRing R] (hI : (IsLocalRing.maximalIdeal R).FG) :
    IsNoetherianRing (GradedReesRing R (IsLocalRing.maximalIdeal R)) := by
  let : IsNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    inferInstanceAs (IsNoetherianRing (IsLocalRing.ResidueField R))
  exact isNoetherianRing_gradedReesRing_of_fg R (IsLocalRing.maximalIdeal R) hI

end SerrePositivity.HilbertSamuel
