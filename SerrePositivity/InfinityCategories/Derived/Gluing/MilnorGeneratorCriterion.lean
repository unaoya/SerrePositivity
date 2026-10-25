module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorNativePretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGFunctorThickHomCriterion
public import SerrePositivity.KST.SConstruction.DGAlgebraEnvelopeGenerator
/-!
概要：元小 Perf 対角の全 Hom 準同型性を、同じ実自由代表の End へ帰着する。
方針：D-17 の元関手に対する生成判定へ、既存の代数自由生成を代入する。
規約：元の対角関手を変更せず、自由対象上の比較は別の具体的証明として残す。
使われ方：Milnor 自由 Hom 比較を全 Perf 対角へ拡張する最後の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
abbrev dgGluingMilnorSourceGenerator :=
  dgSmallPerfectBaseRepresentable R (dgAlgebraCategory R d.source) (dgOdotInputSourcePoint R d)
lemma dgGluingMilnorSourceGenerator_generates :
    modulePerfectOver R (DGSmallPerfectBase R (dgAlgebraCategory R d.source))
      {dgGluingMilnorSourceGenerator R d} =
    modulePerfect R (DGSmallPerfectBase R (dgAlgebraCategory R d.source)) :=
  dgAlgebraEnvelope_perfectOver_representable_eq R d.source Empty
    (dgSmallPerfectBaseFamily R (dgAlgebraCategory R d.source)) (dgOdotInputSourcePoint R d)
lemma dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_generator
    (hb : QuasiIso ((dgOdotQuotientInput R d).diagonal.map
      (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator R d))) :
    HomQuasiIso (dgOdotQuotientInput R d).diagonal :=
  dgFunctor_homQuasiIso_of_singleThickGenerator R _ _ (dgOdotQuotientInput R d).diagonal
    (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator_generates R d) hb
end SerrePositivity.InfinityCategories
