module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotient
public import SerrePositivity.KST.SConstruction.PerfectInvariantHoArrow

/-! # 完備化後の同じ商の二脚の比較
概要：元の商の全関手同型を、完備化後の二脚と Cat^perf の射の類へ移す。
方針：元の比較を同じ完備化で後合成し、完全関手の関手同型不変性を使う。
規約：完備化後の射を厳密 Verdier 商とは扱わない。使われ方：LT の coherent 四角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 完備化後も、元の二脚の比較は全関手同型として存在する。 -/
def legsIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.cSource.hom ≫ d.cLeg.hom)
    (d.dSource.hom ≫ d.dLeg.hom) := by
  simpa only [cSource, dSource, cLeg, dLeg, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientLegsIso p q d.inclusion d.rawProjection d.isVerdier) d.completion.hom

/-- Cat^perf 内で、元の射影と完備化後の二脚の類が可換する。 -/
lemma legs_comm :
    perfectStableHoArrow d.cSource d.left_complete d.c_complete ≫
        perfectStableHoArrow d.cLeg d.c_complete d.right_complete =
      perfectStableHoArrow d.dSource d.left_complete d.d_complete ≫
        perfectStableHoArrow d.dLeg d.d_complete d.right_complete := by
  rw [← perfectStableHoArrow_comp, ← perfectStableHoArrow_comp]
  exact perfectStableHoArrow_eq_of_functorIso d.left_complete d.right_complete d.legsIso

/-- 同じ Cat^perf 関手による像でも、二脚は h Sp 内で可換する。 -/
lemma value_legs_comm (F : perfectStableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    perfectInvariantHoArrow F d.cSource d.left_complete d.c_complete ≫
        perfectInvariantHoArrow F d.cLeg d.c_complete d.right_complete =
      perfectInvariantHoArrow F d.dSource d.left_complete d.d_complete ≫
        perfectInvariantHoArrow F d.dLeg d.d_complete d.right_complete := by
  rw [← perfectInvariantHoArrow_comp, ← perfectInvariantHoArrow_comp]
  exact perfectInvariantHoArrow_eq_of_functorIso F d.left_complete d.right_complete d.legsIso

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
