module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentation

/-!
概要：全頂点を被覆する底変換による表現条件の反映。
方針：制限した fiber 比較を引き戻しの fiber 同型で計算する。
規約：比較の厳密な延長は仮定せず、実際の四角形について判定する。
使われ方：Kerodon Lemma 5.6.8.5（Tag 02SE）、境界固定延長の表現条件。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：底変換した四角形の fiber 比較は元の比較に標準 fiber 同型を前合成する。
方針：普遍 fiber への包含後に計算する。
規約：fiber の同値性を要求しない。
使われ方：表現条件の底変換による保存と反映。 -/
lemma LeftTransportSquare.restrict_pointedFiberMap {E B D : SSet.{u + 1}}
    {p : E ⟶ B} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (g : D ⟶ B) (d : D _⦋0⦌) :
    (S.restrict g).pointedFiberMap d = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d).hom ≫
      S.pointedFiberMap (g.app _ d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection ((g ≫ S.diagram).app _ d)
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd p g) d ≫ (S.restrict g).pointedMap :=
      (S.restrict g).pointedFiberMap_ι d
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (g.app _ d) ≫ S.pointedMap) := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]
      rfl
    _ = _ := by
      rw [Category.assoc]
      exact congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d).hom ≫ f)
        (S.pointedFiberMap_ι (g.app _ d)).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.LeftTransportSquare (restrict_pointedFiberMap)


/-- 概要：任意の底変換は四角形の表現条件を保つ。
方針：元の表現を制限して同じ四角形を回収する。
規約：元の底の quasicategory 性は不要。
使われ方：表現条件を全頂点を含む部分底で検査する。 -/
lemma LeftTransportSquare.isRepresentation_restrict {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (hS : S.IsRepresentation)
    (g : D ⟶ B) : (S.restrict g).IsRepresentation := by
  intro d
  rw [S.restrict_pointedFiberMap]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d)).isQCatEquivalence.comp (hS _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.LeftTransportSquare (isRepresentation_restrict)


/-- 概要：全頂点を被覆する底変換上の表現条件は元の表現条件と同値。
方針：各頂点の持ち上げを選び、fiber 同型を消去する。
規約：底変換は単射でなくてもよい。
使われ方：Kerodon Lemma 5.6.8.5（Tag 02SE） の空間値版、境界固定延長の条件回収。 -/
lemma LeftTransportSquare.isRepresentation_iff_restrict_of_vertexSurjective
    {E B D : SSet.{u + 1}} {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌))) :
    S.IsRepresentation ↔ (S.restrict g).IsRepresentation := by
  refine ⟨fun h ↦ S.isRepresentation_restrict h g, ?_⟩
  intro h b
  obtain ⟨d, rfl⟩ := hg b
  have hd := h d
  rw [S.restrict_pointedFiberMap] at hd
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d)).isQCatEquivalence.cancel_left hd

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction.LeftTransportSquare (isRepresentation_iff_restrict_of_vertexSurjective)


/-- 概要：四角形の頂点が表現空間に属することはその fiber 条件と同値。
方針：実際の表現を回収し、頂点対応の単射性を使う。
規約：周囲の四角形の空間の頂点として判定する。
使われ方：周囲の持ち上げを表現空間の持ち上げへ制限する。 -/
lemma isTransportWitnessVertex_iff_isRepresentation {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) ↔ S.IsRepresentation := by
  constructor
  · rintro ⟨R, hR⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_injective p hR
    rw [← h]
    exact R.toSquare_isRepresentation
  · intro hS
    exact ⟨S.toRepresentation hS, congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex
      (S.toRepresentation_toSquare hS)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction
