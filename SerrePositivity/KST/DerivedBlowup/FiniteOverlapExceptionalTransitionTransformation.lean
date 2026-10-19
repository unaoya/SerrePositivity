module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalVertex
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleTransitionUnit
public import SerrePositivity.KST.DerivedBlowup.GradedNaturalWhiskering

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の包含に対応する局所埋め込み間の指定の全次数自然変換。
方針：目標代数の単位矢を成分に使い、図式係数圏での左右作用の自然性を適用する。
規約：単位複体パラメータの GradedNatTrans として全次数の自然性を保持する。
使われ方：図式加群への作用から canonical な cartesian 比較を構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 局所化環の Hom と図式係数圏の全次数自然性を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環と基底環のモノイダル複体を照合するために必要。
/-- 概要：局所埋め込みから遷移後の局所埋め込みへの標準単位矢の全次数自然変換。
方針：成分を目標代数の単位矢にし、一対象の Hom 上で一般の自然性を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）、指定の包含射の単位から構成する。
使われ方：各図式加群の canonical な局所遷移比較。 -/
def finiteOverlapExceptionalTransitionGradedNatTrans (a : I → R) {T U : FiniteOverlapIndex I}
  (h : T ≤ U) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (finiteOverlapExceptionalVertexDGFunctor R a T)
      (EnrichedFunctor.comp (Complex R)
        (finiteOverlapExceptionalBaseDGTransition R a (finiteOverlapIndexPivot T)
          (finiteOverlapIndexPivot U)
          h (finiteOverlapIndexPivot_mem T)) (finiteOverlapExceptionalVertexDGFunctor R a U))
            where
  app _ := diagramModuleTransitionUnit (finiteOverlapExceptionalDGAlgebraDiagram R a) h
  naturality x y := by
    cases x
    cases y
    let F := finiteOverlapExceptionalDGAlgebraDiagram R a
    change (β_ (𝟙_ (Complex R)) (F.obj T).X).hom ≫
      (diagramModuleHomInclusion F (le_refl T) ⊗ₘ diagramModuleTransitionUnit F h) ≫
        diagramModuleComp F T T U =
      (diagramModuleTransitionUnit F h ⊗ₘ
        ((F.map (homOfLE h)).hom ≫ diagramModuleHomInclusion F (le_refl U))) ≫
        diagramModuleComp F T U U
    exact diagramModuleTransitionUnit_natural F h

end SerrePositivity.KST.DerivedBlowup
