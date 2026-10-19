module

public import SerrePositivity.InfinityCategories.F1.TransportSquareTotalIso
public import SerrePositivity.InfinityCategories.F1.TransportSquareRepresentationRestriction
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：底上の全空間の同型で実際の表現空間を厳密に同定する。
方針：各 fiber の同型で表現条件を移し、四角形の同型を全部分複体へ制限する。
規約：分類図式と全空間の写像を厳密に保持する。
使われ方：積上の表現の制限を実際の底変換の制限へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：全空間の同型による四角形の前合成は各 fiber の同型による前合成。
方針：pointed space の fiber の包含後に fiber の誘導射を計算する。
規約：底の分類図式は変えない。
使われ方：全空間の同型による表現条件の保存と反映。 -/
lemma LeftTransportSquare.totalPre_pointedFiberMap {E F B : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} (S : LeftTransportSquare q)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) :
    (S.totalPre e.hom he).pointedFiberMap b =
      (vertexFiberTotalIso p q e he b).hom ≫ S.pointedFiberMap b := by
  apply vertexFiber_hom_ext pointedSpaceProjection (S.diagram.app _ b)
  have hS : (S.totalPre e.hom he).pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (S.diagram.app _ b) =
      vertexFiberι p b ≫ (e.hom ≫ S.pointedMap) :=
    (S.totalPre e.hom he).pointedFiberMap_ι b
  rw [hS, Category.assoc, S.pointedFiberMap_ι, ← Category.assoc]
  change vertexFiberι p b ≫ (e.hom ≫ S.pointedMap) =
    (vertexFiberMap p q e.hom he b ≫ vertexFiberι q b) ≫ S.pointedMap
  rw [vertexFiberMap_ι, Category.assoc]

/-- 概要：底上の全空間の同型による四角形の前合成は表現条件を保ち反映する。
方針：各 fiber の同型を二対三則で消去する。
規約：比較する二射影は left fibration。
使われ方：四角形の同型を表現空間へ制限する。 -/
lemma LeftTransportSquare.isRepresentation_totalPre_iff {E F B : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [LeftFibration p] [LeftFibration q]
    (S : LeftTransportSquare q) (e : E ≅ F) (he : e.hom ≫ q = p) :
    (S.totalPre e.hom he).IsRepresentation ↔ S.IsRepresentation := by
  constructor
  · intro h b
    have h' := h b
    rw [S.totalPre_pointedFiberMap e he b] at h'
    exact (qCatEquivalenceOfIso (vertexFiberTotalIso p q e he b)).isQCatEquivalence.cancel_left h'
  · intro h b
    rw [S.totalPre_pointedFiberMap e he b]
    exact (qCatEquivalenceOfIso (vertexFiberTotalIso p q e he b)).isQCatEquivalence.comp (h b)

/-- 概要：全空間の同型の四角形の比較は表現の頂点条件を保ち反映する。
方針：四角形の頂点を回収して fiber ごとの表現条件を比較する。
規約：頂点の存在を仮定しない。
使われ方：表現空間の全部分複体の同型。 -/
lemma isTransportWitnessVertex_totalIso_iff {E F B : SSet.{u + 1}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ F) (he : e.hom ≫ q = p) (v : (transportSquareSpace q) _⦋0⦌) :
    IsTransportWitnessVertex q v ↔ IsTransportWitnessVertex p
      ((transportSquareTotalIso p q e he).hom.app _ v) := by
  let S := transportSquareOfVertex q v
  have hS : transportSquareVertex S = v := transportSquareVertex_ofVertex q v
  rw [← hS]
  change IsTransportWitnessVertex q (transportSquareVertex S) ↔ IsTransportWitnessVertex p
    ((transportSquareTotalPre p q e.hom he).app _ (transportSquareVertex S))
  rw [transportSquareTotalPre_vertex, isTransportWitnessVertex_iff_isRepresentation,
    isTransportWitnessVertex_iff_isRepresentation, S.isRepresentation_totalPre_iff]

/-- 概要：底上の全空間の同型は実際の表現空間の厳密な同型を与える。
方針：四角形の同型を表現条件の全部分複体へ制限する。
規約：小ささや非空性の追加仮定は不要。
使われ方：引き戻しと積の表現空間を厳密に翻訳する。 -/
def transportWitnessTotalIso {E F B : SSet.{u + 1}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ F) (he : e.hom ≫ q = p) : transportWitnessSpace q ≅ transportWitnessSpace p :=
  fullSubcomplexIso (transportSquareTotalIso p q e he) (IsTransportWitnessVertex q)
    (IsTransportWitnessVertex p) (isTransportWitnessVertex_totalIso_iff p q e he)

/-- 概要：全空間の同型による表現空間の同型は周囲の四角形の前合成を回収する。
方針：全部分複体の同型の包含公式。
規約：底側と全空間側の全高次データを保持する。
使われ方：パラメーター制限と実際の底変換の制限の可換性。 -/
lemma transportWitnessTotalIso_hom_ι {E F B : SSet.{u + 1}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ F) (he : e.hom ≫ q = p) :
    (transportWitnessTotalIso p q e he).hom ≫ transportWitnessSpaceι p =
      transportWitnessSpaceι q ≫ transportSquareTotalPre p q e.hom he := rfl

end SerrePositivity.InfinityCategories
