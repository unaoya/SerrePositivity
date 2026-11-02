module
public import SerrePositivity.KST.SConstruction.PerfectDGDerivedComparison
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph

/-! # 実 Perf dg 延長の H⁰ による Morita 比較
概要：主導来延長の Perf 制限と実 dg 関手の H⁰ を自然に照合する。
方針：主導来圏の実比較を充満な Perf に戻し、同値の合成判定を使う。
規約：H⁰ 同値だけから全 Hom の擬同型を結論しない。使われ方：全次数判定への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元の主導来延長の Perf 制限と、実 dg 延長の H⁰ の自然比較。 -/
def perfectDGExtensionPerfectComparison :
    perfectDGModuleToPerfect A D Set.univ ⋙ quasiEquivalencePerfectExtension A D E F ≅
      (perfectDGExtension A D E F).onHomotopy ⋙ perfectDGModuleToPerfect A E Set.univ :=
  NatIso.ofComponents
    (fun X => (modulePerfect A E).isoMk (perfectDGDerivedComparisonAt A D E F X))
    (by
      intro X Y f
      apply (modulePerfect A E).hom_ext
      exact perfectDGDerivedComparisonAt_naturality A D E F f)

/-- 主 Perf 作用が同値なら、元の実 dg 延長の H⁰ も同値。 -/
lemma perfectDGExtensionHomotopy_isEquivalence
    [(quasiEquivalencePerfectExtension A D E F).IsEquivalence] :
    (perfectDGExtension A D E F).onHomotopy.IsEquivalence := by
  have : ((perfectDGExtension A D E F).onHomotopy ⋙
      perfectDGModuleToPerfect A E Set.univ).IsEquivalence :=
    Functor.isEquivalence_of_iso (perfectDGExtensionPerfectComparison A D E F)
  exact Functor.isEquivalence_of_comp_right
    (perfectDGExtension A D E F).onHomotopy (perfectDGModuleToPerfect A E Set.univ)

end SerrePositivity.KST.SConstruction
