module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistGauge
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureModule

/-!
概要：KST §3.1 の O(m) を全有限重なり上の実際の dg 加群として構成する。
方針：構造図式加群を、推移単元の整数冪から証明した dg 自己関手に沿って制限する。
規約：各頂点の値だけでなく全次数の作用を持つ。cartesian・perfect 性は別の証明義務。
使われ方：射影空間と導来 blowup の捻りの大域実現。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：全有限重なり上の指定 O(m) の実際の dg 加群。
方針：構造加群の全次数作用を指定 Hom gauge で前合成する。
規約：KST §3.1。使われ方：局所の可逆単元による捻りを大域加群で扱う。 -/
def finiteOverlapTwistRawModule (a : I → R) (m : ℤ) :
    RightModule R (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ :=
  restrictModule R _ _ (finiteOverlapTwistDGFunctor R a m).op.op
    (diagramStructureRawModule (finiteOverlapDGAlgebraDiagram R a))

/-- 概要：指定捻り加群の頂点での値は局所 dg 代数の複体。
方針：Hom gauge は対象を固定するため、構造加群の値の公式を使える。
規約：KST §3.1、捻りは値ではなく遷移に現れる。
使われ方：局所 regular 比較と perfect 性の証明の入力。 -/
theorem finiteOverlapTwistRawModule_obj (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :
    (finiteOverlapTwistRawModule R a m).obj (op (op ⟨T⟩)) =
      ((finiteOverlapDGAlgebraDiagram R a).obj T).X :=
  diagramStructureRawModule_obj (finiteOverlapDGAlgebraDiagram R a) T

/-- 概要：指定 O(m) を通常の全図式加群圏へ包んだ対象。
方針：実際に構成した raw dg 加群を閉零圏へ送る。
規約：KST §3.1。使われ方：主導来局所化への入力。 -/
def finiteOverlapTwistModule (a : I → R) (m : ℤ) :
    AllDiagramModules (finiteOverlapDGAlgebraDiagram R a) :=
  ForgetEnrichment.of (Complex R) (finiteOverlapTwistRawModule R a m)

/-- 概要：指定 O(m) の主導来局所化での対象。
方針：実際の図式加群を指定局所化へ送る。
規約：KST §3.1、cartesian perfect 性の証明とは分ける。
使われ方：捻りの大域導来 Hom と半直交性の後続計算。 -/
def derivedFiniteOverlapTwistModule (a : I → R) (m : ℤ) :
    DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a) :=
  (moduleToDerived R (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj
    (finiteOverlapTwistModule R a m)

end SerrePositivity.KST.DerivedBlowup
