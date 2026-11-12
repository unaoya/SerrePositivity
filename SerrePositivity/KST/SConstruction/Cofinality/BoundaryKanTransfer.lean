module
public import SerrePositivity.KST.SConstruction.Cofinality.BoundaryExInfinityTransfer

/-!
概要：元の Ex∞ 境界比較の次数条件を元の SOA 境界 Kan 射へ移す。
方針：元の SOA から Ex∞ への比較の全基点 π 同型と基点固定成分の自然性を使う。
規約：SOA の厳密な豊穣性を追加仮定にしない。
使われ方：元の境界 K 空間への loop の次数移動。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：Ex∞ 境界射の群条件は元の境界 Kan 射の同じ群条件を与える。
方針：元の二つの Kan 模型の前向き比較をホモトピー可換四角形から消去する。
規約：元の指定完全射の境界 Kan 射を保持する。
使われ方：元の K 群の零次単射・正次数全単射。 -/
lemma boundaryKan_groupConditions_of_exInfinity {X Y : StableModel.{u}} (f : X ⟶ Y)
    (h : Function.Injective (pointedHomotopyMap 1 (exInfinityPointedKanMap
      (X := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩)
      (Y := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩)
      ((boundaryReducedRealizationFunctor 0).map f)).hom) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective (pointedHomotopyMap n (exInfinityPointedKanMap
        (X := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩)
        (Y := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩)
        ((boundaryReducedRealizationFunctor 0).map f)).hom)) :
    Function.Injective (pointedHomotopyMap 1 ((boundaryKanRealizationFunctor 0).map f)) ∧
      ∀ n : ℕ, 1 < n →
        Function.Bijective (pointedHomotopyMap n ((boundaryKanRealizationFunctor 0).map f)) := by
  let A : PointedSSetObject.{u} := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩
  let B : PointedSSetObject.{u} := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩
  let p : A ⟶ B := (boundaryReducedRealizationFunctor 0).map f
  let k := PointedKanReplacement.map p
  let β := (exInfinityPointedKanMap p).hom
  let i := pointedSOAExInfinityComparison A
  let j := pointedSOAExInfinityComparison B
  have hi (n : ℕ) : Function.Bijective (pointedHomotopyMap n i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n i.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint i)
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint i)
      ((pointedSOAExInfinityComparison_piIsomorphism A)
        (PointedKanReplacement.obj A.obj).basepoint n)
  have hj (n : ℕ) : Function.Bijective (pointedHomotopyMap n j) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n j.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint j)
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint j)
      ((pointedSOAExInfinityComparison_piIsomorphism B)
        (PointedKanReplacement.obj B.obj).basepoint n)
  have hm (n : ℕ) : (pointedHomotopyMap n β) ∘ (pointedHomotopyMap n i) =
      (pointedHomotopyMap n j) ∘ (pointedHomotopyMap n k) := by
    funext a
    have hs := pointedHomotopyMap_eq_of_component
      (pointedSOAExInfinityComparison_naturality_component p) n
    exact (pointedHomotopyMap_comp n i β a).symm.trans
      ((congrFun hs a).trans (pointedHomotopyMap_comp n k j a))
  constructor
  · apply (Function.Injective.of_comp_iff (hj 1).injective _).mp
    exact (congrArg Function.Injective (hm 1)).mp (h.1.comp (hi 1).injective)
  · intro n hn
    apply (Function.Bijective.of_comp_iff' (hj n) _).mp
    exact (congrArg Function.Bijective (hm n)).mp ((h.2 n hn).comp (hi n))

/-- 概要：元の core S 実現の群条件は同じ元の境界 Kan 射の群条件を与える。
方針：元の商の Ex∞ 比較と元の SOA 比較を合成する。
規約：基点や元の射を置き換えない。
使われ方：元の K 境界射への最後の次数移動。 -/
lemma boundaryKan_groupConditions_of_coreS {X Y : StableModel.{u}} (f : X ⟶ Y)
    (h : ∀ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj X)) _⦋0⦌,
      Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f))
        (x := a) rfl) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f)) (x := a) rfl)) :
    Function.Injective (pointedHomotopyMap 1 ((boundaryKanRealizationFunctor 0).map f)) ∧
      ∀ n : ℕ, 1 < n →
        Function.Bijective (pointedHomotopyMap n ((boundaryKanRealizationFunctor 0).map f)) :=
  boundaryKan_groupConditions_of_exInfinity f (boundaryExInfinity_groupConditions_of_coreS f h)

end SerrePositivity.KST.SConstruction.Cofinality
