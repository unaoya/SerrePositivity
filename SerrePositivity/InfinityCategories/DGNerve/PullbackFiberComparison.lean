module
public import SerrePositivity.InfinityCategories.DGNerve.FiberConeComparison
public import SerrePositivity.InfinityCategories.DGNerve.ComplexCospanPresentation
public import SerrePositivity.InfinityCategories.DGNerve.RebaseCone

/-! # 任意の引き戻し四角形から標準 fiber への比較

概要：複体 dg nerve の任意の引き戻し四角形の頂点から、その cospan の標準 fiber への誘導射は擬同型。
方針：cospan の chain map 表示を抽出し、錐を読み替えて標準 fiber との比較の同型性を適用する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：D4 の標準 fiber による引き戻し判定の必要性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory MonoidalCategory DifferentialGraded HomotopyComparison
open scoped Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：任意の四角形の cospan を実際の三複体・二つの chain map で表示する。
方針：四角形の右上二辺へ cospan の表示を適用する。
規約：HTT §1.2.13。使われ方：比較先の標準 fiber の入力。 -/
abbrev squareCospanPresentation
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) :=
  presentComplexCospan (pullbackCospan F)

/-- 概要：任意の四角形の cospan の標準 fiber。
方針：抽出した二射の差の mapping cone の −1 シフトを取る。
規約：N7c の pullbackFiber を使用。使われ方：任意の引き戻しの頂点の比較先。 -/
def squareStandardFiber
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) : Complex A :=
  pullbackFiber (squareCospanPresentation F).leftMap (squareCospanPresentation F).rightMap

/-- 概要：四角形の錐を、その抽出した標準 cospan の上の錐へ読み替える。
方針：表示の cospan_eq で固定図式だけを合わせる。
規約：錐の写像・頂点は変えない。使われ方：標準 fiber との比較辺の構成。 -/
def squareFiberComparisonCone
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) :
    JoinCone (pullbackCospan (standardFiberSquare (squareCospanPresentation F).leftMap
      (squareCospanPresentation F).rightMap)) :=
  rebaseCone (squareCospanPresentation F).cospan_eq (pullbackCone F)

/-- 概要：四角形の頂点から抽出した標準 fiber への比較辺。
方針：標準 cospan へ読み替えた錐の比較辺を使う。
規約：四角形の極限性は構成には不要。使われ方：誘導射そのもののホモトピー類。 -/
def squareFiberComparisonEdge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) :
    SSet.Truncated.Edge (X := twoTruncation A (Complex A))
      (pullbackCone F).vertex (Simplex.vertex (squareStandardFiber F)) :=
  fiberConeComparisonCanonicalEdge (squareCospanPresentation F).leftMap
    (squareCospanPresentation F).rightMap (squareFiberComparisonCone F)

/-- 概要：任意の四角形の頂点からその標準 fiber への実際の chain map。
方針：比較辺の閉零射を chain map へ移す。
規約：追加の図式一致の仮定はない。使われ方：N7e の擬同型となる誘導射。 -/
def squareFiberComparison
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) :
    (pullbackCone F).vertex.obj 0 ⟶ squareStandardFiber F :=
  edgeChainMap (squareFiberComparisonEdge F)

/-- 概要：引き戻し四角形の読み替えた錐は標準 cospan 上の極限錐。
方針：引き戻し性の定義と等しい図式への極限性の移送を使う。
規約：HTT §1.2.13。使われ方：比較辺の同型性の前提。 -/
lemma squareFiberComparisonCone_isLimit
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) (hF : IsPullbackSquare F) :
    IsLimitCone (squareFiberComparisonCone F) :=
  rebaseCone_isLimit (squareCospanPresentation F).cospan_eq (pullbackCone F) hF

/-- 概要：任意の引き戻し四角形の頂点から標準 fiber への比較辺は nerve のホモトピー圏で同型。
方針：抽出した標準 cospan 上の極限錐へ N7e の比較辺の同型性を適用する。
規約：HTT §1.2.13、極限の一意性。使われ方：D4 の比較射の同型性。 -/
lemma squareFiberComparison_nerve_isIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) (hF : IsPullbackSquare F) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (squareFiberComparisonEdge F)) :=
  fiberConeComparisonCanonicalEdge_isIso (squareCospanPresentation F).leftMap
    (squareCospanPresentation F).rightMap _ (squareFiberComparisonCone_isLimit F hF)

/-- 概要：任意の引き戻し四角形の比較射の H⁰ の類は同型。
方針：N3 の H⁰ 比較を同じ比較辺の類に適用する。
規約：HA §1.3.1、Kerodon §2.5.3。使われ方：通常の複体ホモトピー圏との比較。 -/
lemma squareFiberComparison_H0_isIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) (hF : IsPullbackSquare F) :
    IsIso ((toHomotopy A (Complex A)).map (edgeClosed (squareFiberComparisonEdge F))) :=
  fiberConeComparisonEdge_H0_isIso (squareCospanPresentation F).leftMap
    (squareCospanPresentation F).rightMap _ (squareFiberComparisonCone_isLimit F hF)

/-- 概要：任意の引き戻し四角形の頂点から標準 fiber への誘導射はホモトピー同値。
方針：比較辺の同型性を N3 と複体ホモトピー圏の同型の特徴づけへ渡す。
規約：任意の可換環・非有界複体。使われ方：擬同型性より強い比較の帰結。 -/
lemma squareFiberComparison_homotopyEquivalence
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) (hF : IsPullbackSquare F) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} A) (.up ℤ) (squareFiberComparison F) :=
  fiberConeComparison_homotopyEquivalence (squareCospanPresentation F).leftMap
    (squareCospanPresentation F).rightMap _ (squareFiberComparisonCone_isLimit F hF)

/-- 概要：任意の引き戻し四角形の頂点から標準 fiber への誘導射は擬同型。
方針：同じ誘導射のホモトピー同値からホモロジー上の同型性を得る。
規約：四角形の IsPullbackSquare 以外の追加前提はない。使われ方：D4 と G1 への比較定理。 -/
lemma squareFiberComparison_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Complex A)) (hF : IsPullbackSquare F) :
    QuasiIso (squareFiberComparison F) :=
  fiberConeComparison_quasiIso (squareCospanPresentation F).leftMap
    (squareCospanPresentation F).rightMap _ (squareFiberComparisonCone_isLimit F hF)

end SerrePositivity.InfinityCategories.DGNerve
