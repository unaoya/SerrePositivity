module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramLocallyPerfect

/-!
概要：KST §3.1 の指定導来比較射による cartesian 条件と局所 perfect 条件の接続。
方針：構成済みの canonical な導来係数拡大比較射の可逆性を全包含で要求する。
規約：対象ごとの条件の定義。自然性・三重整合性・層の降下比較は別に残す。
使われ方：導来 blowup の coherent な Perf 候補の対象条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：全有限重なりの包含について指定導来係数拡大比較が可逆である条件。
方針：存在する任意同型ではなく、単位矢と延長–制限随伴で構成した射を使う。
規約：KST §3.1、underlying 基底加群の制限が擬同型という条件ではない。
使われ方：coherent な図式加群模型の cartesian 対象条件。 -/
def diagramCartesian (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :=
  fun X => ∀ (T U : FiniteOverlapIndex I) (h : T ≤ U),
    IsIso (finiteOverlapDerivedExtensionComparison R a h X)

/-- 概要：指定比較に関して cartesian な導来図式加群の充満部分圏。
方針：主導来局所化の対象を定義した条件で制限する。
規約：KST §3.1、同型不変性と層の降下比較は後続で検証する。
使われ方：導来 blowup の大域加群模型の候補。 -/
abbrev CartesianDerivedDiagramModules (a : I → R) := (diagramCartesian R a).FullSubcategory

/-- 概要：cartesian かつ各有限重なりで perfect な導来図式加群の条件。
方針：指定比較の可逆性と実際の導来局所評価による perfect 性を組み合わせる。
規約：KST §3.1。使われ方：大域 Perf 候補の導来対象条件。 -/
def diagramCartesianPerfect (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :=
  fun X => diagramCartesian R a X ∧ diagramLocallyPerfect R a X

/-- 概要：射影的な図式加群に cartesian・局所 perfect 条件を課す性質。
方針：実際の射影的 dg 加群の主導来像に二つの条件を適用する。
規約：KST §3.1。使われ方：導来 mapping 複体を保持する Perf 候補の対象。 -/
def projectiveDiagramCartesianPerfect (a : I → R)
    (M : ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a)) : Prop :=
  diagramCartesianPerfect R a ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj
    (ForgetEnrichment.of (Complex R) M.val))

/-- 概要：指定の cartesian・局所 perfect 条件を満たす射影的図式加群の充満 dg 部分圏。
方針：全次数の導来 Hom を計算する射影的模型の Hom をそのまま制限する。
規約：KST §3.1、まだ層レベル Perf や dg 商との同値を主張しない候補模型。
使われ方：降下・比較を証明して導来 blowup の Perf に接続する。 -/
abbrev CartesianPerfectDiagramDGModel (a : I → R) :=
  DGFullSubcategory (ProjectiveDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (projectiveDiagramCartesianPerfect R a)

end SerrePositivity.KST.DerivedBlowup
