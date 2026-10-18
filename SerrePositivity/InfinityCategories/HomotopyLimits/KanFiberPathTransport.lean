module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberPost
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanRelativePathLifting

/-!
概要：底の可逆 path に沿って Kan fibration の fiber と任意の射の導来 fiber を同値で移す。
方針：path の全空間への射の指定 path 上の fiber から、二つの端点評価を取る。
規約：fiber の非空性や可縮性を要求せず、元の底の path を指定する。
使われ方：Kerodon 4.5.3.24・7.5.4.6、HTT 4.2.4.1、同値な標的での任意の固定点の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Kan fibration は可逆 path 空間上にも Kan fibration を誘導する。
方針：指定端点の相対 path 射の自明 Kan fibration 性と引き戻し射影の fibration 性を合成する。
規約：元の全空間と底の Kan 性を明示する。
使われ方：Kerodon 4.5.3.24、path の持ち上げ空間を Kan な fiber として扱う。 -/
instance kanEquivalencePathMap_fibration {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] : Fibration (equivalencePathMap p) := by
  have ht := relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p 0
  have : Fibration (relativeEquivalencePathMapAt p 0) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    intro A B j hj
    exact ht.mem j (J_le_monomorphisms _ hj)
  have : Fibration (pullback.fst (equivalencePathEndpoint B 0) p) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
    exact (MorphismProperty.rlp _).pullback_fst _ _
      ((SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance)
  have hf : Fibration (relativeEquivalencePathMapAt p 0 ≫
      pullback.fst (equivalencePathEndpoint B 0) p) := inferInstance
  simpa only [relativeEquivalencePathMapAt_fst] using hf

/-- 概要：指定した底の path の持ち上げの空間から、その指定端点上の fiber への実際の射。
方針：path の射と端点評価の自然な正方形を頂点 fiber の射へ移す。
規約：端点 j は 0 または 1。定義自体には充填性は不要。
使われ方：Kerodon 4.5.3.24、両端点の fiber の共通の比較空間。 -/
def kanFiberPathEndpointMap {E B : SSet.{u}} (p : E ⟶ B)
    (e : (equivalencePath B) _⦋0⦌) (j : Fin 2) :
    vertexFiber (equivalencePathMap p) e ⟶
      vertexFiber p ((equivalencePathEndpoint B j).app _ e) :=
  vertexFiberSquareMap (equivalencePathMap p) p (equivalencePathEndpoint E j)
    (equivalencePathEndpoint B j) (equivalencePathMap_endpoint p j) e

/-- 概要：底の path の持ち上げの空間から両端点の fiber への実際の評価はホモトピー同値。
方針：全空間と底の端点評価の同値性を Kan fibration の fiber の正方形へ適用する。
規約：fiber の非空性や可縮性は要求しない。
使われ方：Kerodon 4.5.3.24・7.5.4.6、底の点を path に沿って移す同値の構成。 -/
lemma kanFiberPathEndpointMap_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : (equivalencePath B) _⦋0⦌) (j : Fin 2) :
    IsSimplicialHomotopyEquivalence (kanFiberPathEndpointMap p e j) := by
  have : TrivialKanFibration (equivalencePathEndpoint E j) := by
    fin_cases j
    · change TrivialKanFibration (equivalencePathEndpoint E 0)
      infer_instance
    · change TrivialKanFibration (equivalencePathEndpoint E 1)
      infer_instance
  have : TrivialKanFibration (equivalencePathEndpoint B j) := by
    fin_cases j
    · change TrivialKanFibration (equivalencePathEndpoint B 0)
      infer_instance
    · change TrivialKanFibration (equivalencePathEndpoint B 1)
      infer_instance
  have he : IsSimplicialHomotopyEquivalence (equivalencePathEndpoint E j) :=
    (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have hb : IsSimplicialHomotopyEquivalence (equivalencePathEndpoint B j) :=
    (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  exact vertexFiberSquareMap_homotopyEquivalence _ _ _ _ _ he hb e

/-- 概要：Kan fibration の底の指定した可逆 path の両端の fiber は同値。
方針：指定 path の持ち上げ空間からの二つの端点評価の同値を合成する。
規約：逆射の選択を含む同値であり、path の合成に関する厳密な関手性は主張しない。
使われ方：Kerodon 4.5.3.24、標的の同値の逆で固定点を回収する際の移送。 -/
def kanFiberPathEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e : (equivalencePath B) _⦋0⦌) :
    QCatEquivalence (vertexFiber p ((equivalencePathEndpoint B 0).app _ e))
      (vertexFiber p ((equivalencePathEndpoint B 1).app _ e)) :=
  (kanFiberPathEndpointMap_homotopyEquivalence p e 0).isQCatEquivalence.choose.symm.trans
    (kanFiberPathEndpointMap_homotopyEquivalence p e 1).isQCatEquivalence.choose

/-- 概要：Kan 複体間の任意の比較射の導来 fiber は底の指定した可逆 path の両端で同値。
方針：元の比較射の path 置換の fibration に fiber の path 移送を適用する。
規約：元の射 p に fibration 性を要求せず、固定点間の path を入力に取る。
使われ方：HTT 4.2.4.1、標的の同値の像と元の底の点の間の直接の fiber 比較。 -/
def comparisonFiberPathEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) (e : (equivalencePath B) _⦋0⦌) :
    QCatEquivalence (comparisonFiber p ((equivalencePathEndpoint B 0).app _ e))
      (comparisonFiber p ((equivalencePathEndpoint B 1).app _ e)) :=
  kanFiberPathEquivalence (equivalencePathReplacementMap p) e

end
end SerrePositivity.InfinityCategories.HomotopyLimits
