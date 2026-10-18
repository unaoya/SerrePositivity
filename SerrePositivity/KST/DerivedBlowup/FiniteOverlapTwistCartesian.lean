module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistLocal
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureCartesian
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraCartesianConditions

/-!
概要：KST Def3.1・Lemma3.6 の全有限重なり上の O(m) の cartesian perfect 性。
方針：一般の gauge 構造加群の指定係数拡大比較の証明を整数冪の gauge へ適用する。
規約：元の Koszul 模型の指定比較へ戻す。層レベルの O(m) との比較は別工程。
使われ方：導来 blowup の大域 Perf 候補における全整数捻りの実現。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：実際の O(m) は正規表示の canonical な比較に関して cartesian。
方針：具体的な整数冪 gauge に一般の指定比較の可逆性を適用する。
規約：KST Def3.1・Lemma3.6。使われ方：元の Koszul 比較との接続。 -/
theorem derivedFiniteOverlapTwistModule_algebraCartesian (a : I → R) (m : ℤ) :
    diagramAlgebraCartesian (finiteOverlapDGAlgebraDiagram R a)
      (derivedFiniteOverlapTwistModule R a m) :=
  diagramGaugeStructureModule_cartesian (finiteOverlapDGAlgebraDiagram R a)
    (finiteOverlapTwistGauge R a m)

/-- 概要：実際の O(m) は元の Koszul 模型の指定係数拡大比較でも cartesian。
方針：正規表示と元の指定比較の可逆性の同値を使う。
規約：KST Def3.1・Lemma3.6。使われ方：既存の大域候補の cartesian 条件。 -/
theorem derivedFiniteOverlapTwistModule_cartesian (a : I → R) (m : ℤ) :
    diagramCartesian R a (derivedFiniteOverlapTwistModule R a m) :=
  (finiteOverlapAlgebraCartesian_iff R a _).mp
    (derivedFiniteOverlapTwistModule_algebraCartesian R a m)

/-- 概要：実際に構成した全整数の O(m) は元の有限重なり模型で cartesian perfect。
方針：指定係数拡大比較の可逆性と証明済み局所 regular 性を合わせる。
規約：KST Def3.1・Lemma3.6。使われ方：大域 Perf 候補への捻り対象の所属。 -/
theorem derivedFiniteOverlapTwistModule_cartesianPerfect (a : I → R) (m : ℤ) :
    diagramCartesianPerfect R a (derivedFiniteOverlapTwistModule R a m) :=
  ⟨derivedFiniteOverlapTwistModule_cartesian R a m,
    derivedFiniteOverlapTwistModule_locallyPerfect R a m⟩

end SerrePositivity.KST.DerivedBlowup
