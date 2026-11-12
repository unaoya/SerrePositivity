module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalBoundaryTotalIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRepresentationRestriction

/-!
概要：境界上の可換四角形のデータを両端の対象と fiber 写像へ展開する。
方針：境界の定値単体と引き戻しの fiber 同型を使う。
規約：両側の射を厳密に回収する。
使われ方：実際の境界表現から可縮性定理の端点データを得る。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

local instance {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p (boundary 1).ι) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p (boundary 1).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：区間境界上の射は二つの頂点での値から厳密に回収される。
方針：各境界単体の定値性と射の自然性を使う。
規約：標的の充填性は不要。
使われ方：指定された境界の分類図式の端点表示。 -/
lemma intervalMappingBoundary_eta {X : SSet.{u}} (F : (boundary 1 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 0))
      (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 1)) = F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  ext z
  have hz (i : Fin 2) (hi : z.val 0 = i) :
      (boundary 1 : SSet.{u}).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i) = z := by
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant z j).trans hi).symm
  change (if z.val 0 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 0)) n
    else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 1)) n) = _
  split_ifs with hi
  · have h := F.naturality_apply (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 0)
    rw [hz 0 hi] at h
    exact h.symm
  · have hi₁ : z.val 0 = 1 := Fin.eq_one_of_ne_zero _ hi
    have h := F.naturality_apply (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex 1)
    rw [hz 1 hi₁] at h
    exact h.symm

/-- 概要：境界上の四角形から元の端点 fiber の普遍 pointed-space fiber への写像を取る。
方針：引き戻しの fiber 同型の逆に四角形の fiber 比較を続ける。
規約：元の端点 fiber を定義域にする。
使われ方：両端同値を指定した区間族の入力。 -/
def LeftTransportSquare.intervalBoundaryFiberMap {E : SSet.{u + 1}}
    {p : E ⟶ (Δ[1] : SSet.{u + 1})}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (pullback.snd p (boundary 1).ι)) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm i) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p (boundary 1).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i)).inv ≫
    S.pointedFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftTransportSquare (intervalBoundaryFiberMap)


/-- 概要：境界四角形の端点写像は指定された全空間側の射を厳密に回収する。
方針：fiber 比較の包含公式と引き戻し fiber 同型の逆の定義。
規約：射の等式であり同値類の一致ではない。
使われ方：境界の pointed space 値図式の端点表示。 -/
lemma LeftTransportSquare.intervalBoundaryFiberMap_ι {E : SSet.{u + 1}}
    {p : E ⟶ (Δ[1] : SSet.{u + 1})}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (pullback.snd p (boundary 1).ι)) (i : Fin 2) :
    S.intervalBoundaryFiberMap i ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFiberLift p i ≫ S.pointedMap := by
  rw [LeftTransportSquare.intervalBoundaryFiberMap, Category.assoc, S.pointedFiberMap_ι,
    ← Category.assoc]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftTransportSquare (intervalBoundaryFiberMap_ι)


/-- 概要：境界上の表現は元の両端 fiber の実際の同値を与える。
方針：引き戻しの fiber 同型の逆と表現の fiber 比較を合成する。
規約：p の left fibration 性だけを要求する。
使われ方：区間族の可縮性への入力条件。 -/
lemma LeftTransportSquare.intervalBoundaryFiberMap_isQCatEquivalence {E : SSet.{u + 1}}
    {p : E ⟶ (Δ[1] : SSet.{u + 1})} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (pullback.snd p (boundary 1).ι))
    (hS : S.IsRepresentation) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (S.intervalBoundaryFiberMap i) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p (boundary 1).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i)).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.comp (hS (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryVertex i))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftTransportSquare (intervalBoundaryFiberMap_isQCatEquivalence)


/-- 概要：境界の全空間側の図式は二つの端点写像から厳密に回収される。
方針：直和の二成分で fiber 比較の包含公式を使う。
規約：分類図式と同時に使える厳密な等式。
使われ方：境界制限の fiber と同時端点条件の fiber を結ぶ。 -/
lemma LeftTransportSquare.intervalBoundaryPointedMap_eq {E : SSet.{u + 1}}
    {p : E ⟶ (Δ[1] : SSet.{u + 1})}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare (pullback.snd p (boundary 1).ι)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryPointedMap (S.intervalBoundaryFiberMap 0) (S.intervalBoundaryFiberMap 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryTotalMap p ≫ S.pointedMap := by
  apply SSet.hom_ext
  intro n
  ext x
  cases x with
  | inl x =>
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (S.intervalBoundaryFiberMap_ι 0) n) x
  | inr x =>
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (S.intervalBoundaryFiberMap_ι 1) n) x

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftTransportSquare (intervalBoundaryPointedMap_eq)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
