module

public import SerrePositivity.KST.DerivedBlowup.AlgebraVertexComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalVertex

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の有限重なりの一対象正規表示と元の例外因子 Koszul 局所模型の比較。
方針：同じ自己 Hom dg 代数からの Hom 恒等比較を局所模型へ適用する。
規約：全 diagram-module の係数圏と有限重なりの係数関手を保持する。
使われ方：正規表示での図式計算を既存の幾何的チャートへ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なりの局所 dg 代数の一対象正規表示。
方針：構成済み係数関手の当該モノイド対象を一対象 dg 圏として読む。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：対象の移送を含まない局所表示。 -/
abbrev FiniteOverlapExceptionalAlgebraVertex (a : I → R) (T : FiniteOverlapIndex I) :=
  AlgebraVertex ((finiteOverlapExceptionalDGAlgebraDiagram R a).obj T)

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環から基底環へ制限した dg 構造と自己 Hom を照合するために必要。
/-- 概要：正規表示から既存の有限重なり Koszul 模型への指定 dg 比較。
方針：標準点の自己 Hom を用いる一般の Hom 恒等関手を適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：既存の局所 perfect 圏との比較。 -/
def finiteOverlapExceptionalAlgebraVertexToChart (a : I → R) (T : FiniteOverlapIndex I) :
    DGFunctor R (FiniteOverlapExceptionalAlgebraVertex R a T)
      (FiniteOverlapExceptionalVertexObject R a T) :=
  algebraVertexToOriginal (R := R) (FiniteOverlapExceptionalVertexObject R a T) .point

set_option synthInstance.maxHeartbeats 100000 in
-- 一対象表示と基底制限後の Koszul 模型の dg 構造を照合するために必要。
/-- 概要：有限重なりの正規表示と元の例外因子 Koszul 模型の比較は dg 準同値。
方針：Hom 恒等比較と元の局所模型の一対象性を使う。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：正規表示への局所導来計算の移送。 -/
theorem finiteOverlapExceptionalAlgebraVertexToChart_quasiEquivalence (a : I → R)
    (T : FiniteOverlapIndex I) :
    QuasiEquivalence (finiteOverlapExceptionalAlgebraVertexToChart R a T) :=
  algebraVertexToOriginalQuasiEquivalence (R := R)
    (FiniteOverlapExceptionalVertexObject R a T) .point
    (fun x => by cases x; rfl)

set_option maxHeartbeats 2000000 in
-- 局所化 dg 模型への Hom 恒等比較と全図式の埋め込みを照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の Hom と一対象表示の Hom を照合するために必要。
/-- 概要：正規表示から全図式係数圏への埋め込みは元の局所埋め込みと整合する。
方針：対象は当該添字で一致し、Hom 上の恒等比較を消去する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：二つの表示による局所加群評価の比較。 -/
theorem finiteOverlapExceptionalAlgebraVertexToChart_embedding (a : I → R)
    (T : FiniteOverlapIndex I) :
    (finiteOverlapExceptionalAlgebraVertexToChart R a T).comp
        (finiteOverlapExceptionalVertexDGFunctor R a T) =
      diagramAlgebraVertexEmbedding (finiteOverlapExceptionalDGAlgebraDiagram R a) T := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change 𝟙 _ ≫
    diagramModuleHomInclusion (finiteOverlapExceptionalDGAlgebraDiagram R a) (le_refl T) = _
  exact Category.id_comp _

end SerrePositivity.KST.DerivedBlowup
