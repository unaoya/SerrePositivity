module

public import SerrePositivity.InfinityCategories.F1.TransportSquareTensorRepresentation
public import SerrePositivity.InfinityCategories.F1.TransportSquareRepresentationRestriction
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexInternalHom

/-!
概要：積上の実際の表現空間は元の表現空間へのパラメーター族と厳密に同型。
方針：四角形の currying 同型を各頂点で表現となる全部分複体へ制限する。
規約：分類図式と全空間の射の全高次データを保持する。
使われ方：区間の境界制限を点上の表現空間の対角の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の currying 同型は表現条件を各パラメーターでの表現条件へ移す。
方針：実際の四角形の頂点を回収し、fiber 同型による表現条件の判定を使う。
規約：パラメーターも底も任意の単体集合。
使われ方：表現空間の全部分複体の同型。 -/
lemma isTransportWitnessVertex_tensor_iff {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (K : SSet.{u + 1})
    (v : (transportSquareSpace (p ▷ K)) _⦋0⦌) :
    IsTransportWitnessVertex (p ▷ K) v ↔
      FunctorVertexSatisfies K (transportSquareSpace p) (IsTransportWitnessVertex p)
        ((transportSquareTensorIso p K).hom.app _ v) := by
  let S := transportSquareOfVertex (p ▷ K) v
  have hS : transportSquareVertex S = v := transportSquareVertex_ofVertex (p ▷ K) v
  change IsTransportWitnessVertex (p ▷ K) v ↔ ∀ k : K _⦋0⦌,
    IsTransportWitnessVertex p ((evaluateFunctorAt k).app _
      ((transportSquareTensorIso p K).hom.app _ v))
  rw [← hS, isTransportWitnessVertex_iff_isRepresentation, S.isRepresentation_tensor_iff]
  apply forall_congr'
  intro k
  rw [transportSquareTensorIso_vertex_at, isTransportWitnessVertex_iff_isRepresentation]

/-- 概要：積上の表現空間は元の表現空間への内部 Hom と厳密に同型。
方針：四角形の同型を全部分複体へ制限し、内部 Hom の全部分複体表示を戻す。
規約：表現の非空性と小ささを仮定しない。
使われ方：Kerodon Lemma 5.6.9.2 の表現の区間族との比較。 -/
def transportWitnessTensorIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (K : SSet.{u + 1}) :
    transportWitnessSpace (p ▷ K) ≅ (ihom K).obj (transportWitnessSpace p) :=
  fullSubcomplexIso (transportSquareTensorIso p K)
    (IsTransportWitnessVertex (p ▷ K))
    (FunctorVertexSatisfies K (transportSquareSpace p) (IsTransportWitnessVertex p))
    (isTransportWitnessVertex_tensor_iff p K) ≪≫
      (fullSubcomplexInternalHomIso K (transportSquareSpace p) (IsTransportWitnessVertex p)).symm

/-- 概要：表現空間の積の同型は周囲の四角形の currying を回収する。
方針：全部分複体の同型と内部 Hom の比較の包含公式を続ける。
規約：全高次単体での厳密な等式。
使われ方：実際の境界制限との自然性を確認する。 -/
lemma transportWitnessTensorIso_hom_ι {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (K : SSet.{u + 1}) :
    (transportWitnessTensorIso p K).hom ≫ (ihom K).map (transportWitnessSpaceι p) =
      transportWitnessSpaceι (p ▷ K) ≫ (transportSquareTensorIso p K).hom := by
  dsimp only [transportWitnessTensorIso, Iso.trans_hom, Iso.symm_hom, transportWitnessSpaceι]
  rw [Category.assoc, fullSubcomplexInternalHomIso_inv_ι, fullSubcomplexIso_hom_ι]

end SerrePositivity.InfinityCategories
