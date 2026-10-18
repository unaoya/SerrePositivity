module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistModule
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeLocal
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureLocalComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraPerfectComparison

/-!
概要：KST Def3.1・Lemma3.6 の大域 O(m) の局所 regular 比較。
方針：Hom gauge の対角恒等性から構造加群との局所同型を作り、perfect 性を移す。
規約：指定係数拡大比較の可逆性と層レベル比較は別の証明義務。
使われ方：捻り対象の局所自由性と後続の cartesian perfect 性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：指定捻り加群は各局所頂点で構造加群と同型。
方針：一般の Hom gauge の局所同型を実際の構造図式加群へ適用する。
規約：KST Def3.1。使われ方：捻り加群の局所 trivialization。 -/
def finiteOverlapTwistLocalIso (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :
    (diagramAlgebraModuleEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj
      (finiteOverlapTwistModule R a m) ≅
    (diagramAlgebraModuleEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj
      (diagramStructureModule (finiteOverlapDGAlgebraDiagram R a)) :=
  diagramGaugeLocalIso (finiteOverlapDGAlgebraDiagram R a) (finiteOverlapTwistGauge R a m)
    (diagramStructureRawModule (finiteOverlapDGAlgebraDiagram R a)) T

/-- 概要：指定捻り加群の局所導来評価は regular 加群の主導来像と同型。
方針：構造加群の指定 regular 同型と局所 trivialization の主導来像を合成する。
規約：KST Def3.1・Lemma3.6。使われ方：局所 perfect 性と導来 Hom 計算。 -/
def finiteOverlapTwistLocalRegularDerivedIso (a : I → R) (m : ℤ)
    (T : FiniteOverlapIndex I) :
    (moduleToDerived R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R)
        (representable R
          (op (.point : AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))))) ≅
    (diagramAlgebraDerivedEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj
      (derivedFiniteOverlapTwistModule R a m) :=
  diagramStructureLocalRegularDerivedIso (finiteOverlapDGAlgebraDiagram R a) T ≪≫
    ((moduleToDerived R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ).mapIso
      (finiteOverlapTwistLocalIso R a m T)).symm

/-- 概要：指定 O(m) は正規化した全局所頂点で perfect。
方針：局所 regular 導来同型に沿って代表生成元の perfect 性を移す。
規約：KST Def3.1・Lemma3.6。使われ方：大域 Perf 候補の局所条件。 -/
theorem derivedFiniteOverlapTwistModule_algebraLocallyPerfect (a : I → R) (m : ℤ) :
    diagramAlgebraLocallyPerfect (finiteOverlapDGAlgebraDiagram R a)
      (derivedFiniteOverlapTwistModule R a m) := by
  intro T
  exact (modulePerfect R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ).prop_of_iso
    (finiteOverlapTwistLocalRegularDerivedIso R a m T)
    (modulePerfectOver_representable R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ
      (op .point) (Set.mem_univ _))

/-- 概要：指定 O(m) は元の Koszul 局所模型でも全有限重なりで perfect。
方針：局所 perfect 条件の表示不変性を使う。
規約：KST Def3.1・Lemma3.6。使われ方：元の cartesian perfect 条件への接続。 -/
theorem derivedFiniteOverlapTwistModule_locallyPerfect (a : I → R) (m : ℤ) :
    diagramLocallyPerfect R a (derivedFiniteOverlapTwistModule R a m) :=
  (finiteOverlapAlgebraLocallyPerfect_iff R a _).mp
    (derivedFiniteOverlapTwistModule_algebraLocallyPerfect R a m)

end SerrePositivity.KST.DerivedBlowup
