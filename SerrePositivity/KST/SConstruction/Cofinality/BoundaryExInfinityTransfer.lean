module
public import SerrePositivity.KST.SConstruction.Cofinality.CoreSPointedBoundary

/-!
概要：元の Ex∞ core S 実現の次数条件を元の境界商の Ex∞ の指定基点へ移す。
方針：任意頂点で基点を付けた元の商の可換四角形の両辺の π 同型を消去する。
規約：同じ元の完全射を保持し、chosen zero の厳密保存は仮定しない。
使われ方：元の SOA 境界 Kan 模型と K 空間への比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：元の境界商の Ex∞ における指定基点の群条件。
方針：元の商比較の両側の全基点 π 同型を可換四角形から消去する。
規約：入力は元の実現射の全基点条件で、出力も同じ元の境界射。
使われ方：元の境界 Kan 射の零次 K・正次数 K の条件。 -/
lemma boundaryExInfinity_groupConditions_of_coreS {X Y : StableModel.{u}} (f : X ⟶ Y)
    (h : ∀ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj X)) _⦋0⦌,
      Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f))
        (x := a) rfl) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f)) (x := a) rfl)) :
    Function.Injective (pointedHomotopyMap 1 (exInfinityPointedKanMap
      (X := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩)
      (Y := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩)
      ((boundaryReducedRealizationFunctor 0).map f)).hom) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective (pointedHomotopyMap n (exInfinityPointedKanMap
        (X := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩)
        (Y := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩)
        ((boundaryReducedRealizationFunctor 0).map f)).hom) := by
  let x : (coreSRealizationFunctor.obj X) _⦋0⦌ := (pointedSRealization X.carrier).basepoint
  let y := (coreSRealizationFunctor.map f).app (Opposite.op ⦋0⦌) x
  let AX := coreSVertexObject X x
  let AY := coreSVertexObject Y y
  let BX : PointedSSetObject.{u} := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩
  let BY : PointedSSetObject.{u} := ⟨(boundaryReducedRealizationFunctor 0).obj Y⟩
  let A := (exInfinityPointedKanEnrichedFunctor.obj AX).obj
  let B := (exInfinityPointedKanEnrichedFunctor.obj AY).obj
  let U := (exInfinityPointedKanEnrichedFunctor.obj BX).obj
  let V := (exInfinityPointedKanEnrichedFunctor.obj BY).obj
  let α : A ⟶ B := (exInfinityPointedKanMap (coreSVertexMap f x)).hom
  let β : U ⟶ V := (exInfinityPointedKanMap
    (X := BX) (Y := BY) ((boundaryReducedRealizationFunctor 0).map f)).hom
  let i : A ⟶ U := (exInfinityPointedKanMap
    (X := AX) (Y := BX) (coreSVertexBoundary X x)).hom
  let j : B ⟶ V := (exInfinityPointedKanMap
    (X := AY) (Y := BY) (coreSVertexBoundary Y y)).hom
  have hi (n : ℕ) : Function.Bijective (pointedHomotopyMap n i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n i.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint i)
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint i)
      ((coreSExInfinityBoundary_piIsomorphism X x) A.basepoint n)
  have hj (n : ℕ) : Function.Bijective (pointedHomotopyMap n j) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n j.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint j)
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint j)
      ((coreSExInfinityBoundary_piIsomorphism Y y) B.basepoint n)
  have hα₁ : Function.Injective (pointedHomotopyMap 1 α) := by
    have ha (z : B.right _⦋0⦌) (hz : α.right.app (Opposite.op ⦋0⦌) A.basepoint = z) :
        Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 α.right hz) := by
      subst z
      exact (h A.basepoint).1
    exact ha B.basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint α)
  have hα (n : ℕ) (hn : 1 < n) : Function.Bijective (pointedHomotopyMap n α) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n α.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint α)
      rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint α) ((h A.basepoint).2 n hn)
  have hs : α ≫ j = i ≫ β := by
    apply Under.UnderMorphism.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp _ _).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (congrArg Under.Hom.right
        (coreSVertexBoundary_naturality f x))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp _ _))
  have hm (n : ℕ) : (pointedHomotopyMap n β) ∘ (pointedHomotopyMap n i) =
      (pointedHomotopyMap n j) ∘ (pointedHomotopyMap n α) := by
    funext a
    exact (pointedHomotopyMap_comp n i β a).symm.trans
      ((congrArg (fun k => pointedHomotopyMap n k a) hs.symm).trans
        (pointedHomotopyMap_comp n α j a))
  constructor
  · apply (Function.Injective.of_comp_iff' _ (hi 1)).mp
    rw [hm 1]
    exact (hj 1).injective.comp hα₁
  · intro n hn
    apply (Function.Bijective.of_comp_iff _ (hi n)).mp
    rw [hm n]
    exact (hj n).comp (hα n hn)

end SerrePositivity.KST.SConstruction.Cofinality
