module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareBaseIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibersBaseIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-!
概要：底の同型で射影を移した実際の表現空間と元の表現空間の同型。
方針：底の同型の fiber 同型で表現条件を保ち反映する。
規約：全空間への射は変更しない。
使われ方：Δ⁰ と区間の積の底を区間へ移す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：底の同型で四角形を移した fiber 比較は底の fiber 同型に沿う前合成。
方針：pointed space の fiber の包含後に二つの比較を同定する。
規約：全空間の写像を厳密に保持する。
使われ方：底の同型による表現条件の移送。 -/
lemma LeftTransportSquare.basePre_pointedFiberMap {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (e : B ≅ D) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ≫ e.hom)) (b : B _⦋0⦌) :
    (S.basePre e.hom rfl).pointedFiberMap b =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso p e b).hom ≫ S.pointedFiberMap (e.hom.app _ b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ (e.hom.app _ b))
  have hS : (S.basePre e.hom rfl).pointedFiberMap b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ (e.hom.app _ b)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ S.pointedMap := (S.basePre e.hom rfl).pointedFiberMap_ι b
  rw [hS, Category.assoc, S.pointedFiberMap_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso_hom_ι]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (basePre_pointedFiberMap)


/-- 概要：底の同型での前合成は四角形の表現条件を保ち反映する。
方針：fiber 同型を二対三則で消去し底の全頂点を同型で被覆する。
規約：射影の left fibration 性以外の存在仮定は不要。
使われ方：四角形の底の同型を表現空間へ制限する。 -/
lemma LeftTransportSquare.isRepresentation_basePre_iff {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : B ≅ D)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (p ≫ e.hom)) :
    (S.basePre e.hom rfl).IsRepresentation ↔ S.IsRepresentation := by
  constructor
  · intro h d
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (e.hom.app (Opposite.op ⦋0⦌))).2 d
    have h' := h b
    rw [S.basePre_pointedFiberMap p e b] at h'
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso p e b)).isQCatEquivalence
      |>.cancel_left h'
  · intro h b
    rw [S.basePre_pointedFiberMap p e b]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso p e b)).isQCatEquivalence
      |>.comp (h (e.hom.app _ b))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (isRepresentation_basePre_iff)


/-- 概要：底の同型による四角形の同型は表現の頂点条件を保ち反映する。
方針：頂点の四角形を回収し表現条件の同値を使う。
規約：頂点の存在は仮定しない。
使われ方：表現空間の全部分複体の同型。 -/
lemma isTransportWitnessVertex_baseIso_iff {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : B ≅ D)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (p ≫ e.hom)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex (p ≫ e.hom) v ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBaseIso p (p ≫ e.hom) e rfl).hom.app _ v) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareOfVertex (p ≫ e.hom) v
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S = v := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_ofVertex (p ≫ e.hom) v
  rw [← hS]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex (p ≫ e.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre p (p ≫ e.hom) e.hom rfl).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.isTransportWitnessVertex_iff_isRepresentation,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.isTransportWitnessVertex_iff_isRepresentation, S.isRepresentation_basePre_iff]

/-- 概要：底の同型で射影を移しても実際の表現空間は厳密に同型。
方針：四角形の底の同型を表現条件の全部分複体へ制限する。
規約：小ささや非空性の仮定を追加しない。
使われ方：区間や境界の底を同型で正規化する。 -/
def transportWitnessBaseIso {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : B ≅ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (p ≫ e.hom) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBaseIso p (p ≫ e.hom) e rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex (p ≫ e.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p)
    (isTransportWitnessVertex_baseIso_iff p e)

/-- 概要：底の同型による表現空間の比較は四角形の分類図式の前合成を回収する。
方針：全部分複体の同型の包含公式。
規約：全空間側の射も全高次単体で保持する。
使われ方：区間境界制限と底の同型の自然性。 -/
lemma transportWitnessBaseIso_hom_ι {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : B ≅ D) :
    (transportWitnessBaseIso p e).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (p ≫ e.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBasePre p (p ≫ e.hom) e.hom rfl := rfl

/-- 概要：指定した射影の可換等式を使う底の同型の表現空間の同型。
方針：射影の等式を消去して底の同型の標準形へ戻す。
規約：等しい射影の二つの left fibration の証明の違いは影響しない。
使われ方：点への唯一の射を使った底の正規化。 -/
def transportWitnessBaseIsoOfComm {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (q : E ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (e : B ≅ D) (he : p ≫ e.hom = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace q ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p := by
  subst q
  exact transportWitnessBaseIso p e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
