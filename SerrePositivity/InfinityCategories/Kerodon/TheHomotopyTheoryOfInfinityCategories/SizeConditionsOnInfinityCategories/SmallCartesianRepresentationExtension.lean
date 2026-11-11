module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessCartesianRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallRepresentationExtension

/-!
概要：小さい全空間の表現の境界固定延長を任意の cartesian な表示に移す。
方針：標準 pullback への制限と全空間の同型で表現空間の全境界充填を移す。
規約：指定した全空間の上の表現を厳密に回収する。
使われ方：相対射の区間実現で両端の和に指定した表現を延長する。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：cartesian 制限の表現の頂点は表現空間の前合成と一致する。
方針：周囲の四角形へ含めて図式と pointed space への射を比較する。
規約：pullback の表示の選択を隠さず両射を保つ。
使われ方：空間上の充填から実際の表現の厳密な延長へ戻す。 -/
lemma transportWitnessPre_cartesianRestrict_vertex {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q.hom) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex (R.cartesianRestrict f.left f.right hf) := by
  apply Subtype.ext
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι f hf)
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare) at h
  refine h.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_vertex]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.ext
  · rfl
  · exact (R.cartesianRestrict_pointedMap _ _ hf).symm

/-- 概要：小さい全空間の cartesian な単射制限は trivial Kan fibration。
方針：標準 pullback への制限の全境界充填を同型で移す。
規約：底の小ささや境界の表現の存在は仮定しない。
使われ方：両端の和などの具体的な全空間の上の相対延長。 -/
lemma smallTransportWitnessPre_trivialKanFibration {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] [∀ n, Small.{u} (q.left.obj n)]
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_eq_restriction_totalIso f hf]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessRestriction_trivialKanFibration q.hom f.right).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：cartesian な単射の上の指定表現を元の小さい全空間へ厳密に延長する。
方針：表現空間の前合成の切断を実際の表現の頂点の全単射へ移す。
規約：標準 pullback の全空間へ指定表現を置き換える必要はない。
使われ方：指定した両端表現から区間実現の表現を得る。 -/
lemma exists_small_cartesianTransportRepresentation_extension {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] [∀ n, Small.{u} (q.left.obj n)]
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p.hom) :
    ∃ S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q.hom, S.cartesianRestrict f.left f.right hf = R := by
  have := smallTransportWitnessPre_trivialKanFibration f hf
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf)
  obtain ⟨S, hS⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_surjective _ (s.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R))
  refine ⟨S, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_injective _ ?_⟩
  rw [← transportWitnessPre_cartesianRestrict_vertex, hS]
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R)) hs

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
