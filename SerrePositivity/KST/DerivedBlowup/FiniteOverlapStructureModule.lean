module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureLocalComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraPerfectComparison

/-!
概要：KST Def3.1・Lemma3.6 の有限重なり図式上の実際の構造 dg 加群。
方針：構造図式加群の一般構成を Koszul 係数図式へ適用し、元の模型の局所 perfect 条件へ戻す。
規約：cartesian 性と層レベル構造層との比較は別に証明する。
使われ方：導来 blowup の構造加群と生成系の入力。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なり Koszul 係数図式上の構造加群。
方針：補助始点の共変 representable の制限による一般構成を使う。
規約：KST Def3.1・Lemma3.6。使われ方：大域構造加群の主導来像。 -/
abbrev blowupStructureModule (a : I → R) :=
  diagramStructureModule (finiteOverlapDGAlgebraDiagram R a)

/-- 概要：有限重なり図式上の構造加群の主導来対象。
方針：実際の構造図式加群の指定主局所化像を使う。
規約：KST Def3.1・Lemma3.6。使われ方：構造加群の大域 Perf 候補での計算。 -/
abbrev derivedBlowupStructureModule (a : I → R) :=
  derivedDiagramStructureModule (finiteOverlapDGAlgebraDiagram R a)

/-- 概要：構成済み構造加群は元の Koszul 局所模型の全有限重なりで perfect。
方針：一般の局所 regular 比較と局所 perfect 条件の表示不変性を合わせる。
規約：KST Def3.1・Lemma3.6、cartesian 性の証明は別。
使われ方：導来 blowup の構造加群の局所 perfect 条件。 -/
theorem derivedBlowupStructureModule_locallyPerfect (a : I → R) :
    diagramLocallyPerfect R a (derivedBlowupStructureModule R a) :=
  (finiteOverlapAlgebraLocallyPerfect_iff R a _).mp
    (diagramStructureModule_locallyPerfect (finiteOverlapDGAlgebraDiagram R a))

end SerrePositivity.KST.DerivedBlowup
