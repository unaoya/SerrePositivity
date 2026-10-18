module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureLocalComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraPerfectComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureCartesian
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraCartesianConditions

/-!
概要：KST Def3.1・Lemma3.6 の有限重なり図式上の実際の構造 dg 加群。
方針：構造図式加群の一般構成を Koszul 係数図式へ適用し、元の模型の局所 perfect 条件へ戻す。
規約：指定比較の可逆性を証明し、層レベル構造層との比較は別工程に残す。
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

/-- 概要：有限重なりの構造加群は元の Koszul 模型の指定比較に関して cartesian。
方針：正規表示での canonical な比較の可逆性と cartesian 条件の表示不変性を使う。
規約：KST Def3.1・Lemma3.6。使われ方：構造加群の大域 Perf 候補への所属。 -/
theorem derivedBlowupStructureModule_cartesian (a : I → R) :
    diagramCartesian R a (derivedBlowupStructureModule R a) :=
  (finiteOverlapAlgebraCartesian_iff R a _).mp
    (diagramStructureModule_cartesian (finiteOverlapDGAlgebraDiagram R a))

/-- 概要：有限重なり上の実際の構造加群は cartesian perfect な導来図式加群。
方針：元の Koszul 模型での cartesian 性と局所 perfect 性を組み合わせる。
規約：KST Def3.1・Lemma3.6、層の構造加群との比較は別工程。
使われ方：導来 blowup の構造加群の射影的 dg 代表を構成する。 -/
theorem derivedBlowupStructureModule_cartesianPerfect (a : I → R) :
    diagramCartesianPerfect R a (derivedBlowupStructureModule R a) :=
  ⟨derivedBlowupStructureModule_cartesian R a, derivedBlowupStructureModule_locallyPerfect R a⟩

end SerrePositivity.KST.DerivedBlowup
