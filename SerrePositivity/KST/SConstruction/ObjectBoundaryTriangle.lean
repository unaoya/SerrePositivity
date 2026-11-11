module
public import SerrePositivity.KST.SConstruction.KZeroFundamentalCalculation
public import SerrePositivity.KST.SConstruction.ObjectSConstruction

/-! # 元の object S₂ の三辺の基本群関係
概要：全 gapped object S から元の Kan 境界商へ写し、二単体の三辺の積を計算する。
方針：既存の object/core 比較と境界比較を合成し、元の二単体を乗法の証拠にする。
規約：第一行の選択模型へ置換しない。使われ方：対象の cofiber 加法関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の全 gapped object S から、一重 S の元の Kan 境界商への比較。 -/
def objectBoundaryKanComparison (X : StableModel.{u}) :
    objectSConstruction X.carrier ⟶ ((boundaryKanRealizationFunctor 0).obj X).right :=
  objectToCoreSRealization X.carrier ≫ iteratedRealizationToKan 0 X

/-- 元の object S の全頂点は境界商の同じ基点へ写る。 -/
lemma objectBoundaryKanComparison_vertex (X : StableModel.{u})
    (z : (objectSConstruction X.carrier) _⦋0⦌) :
    (objectBoundaryKanComparison X).app _ z =
      ((boundaryKanRealizationFunctor 0).obj X).basepoint := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (iteratedRealizationToKan_zeroColumn 0 X) (Opposite.op ⦋0⦌))
      (⟨z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
        (X := sConstruction 0 X.carrier) z⟩ :
        (coreSConstruction 0 X.carrier) _⦋0⦌)
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, diagonalZeroColumn_zero] at h
  change (iteratedRealizationToKan 0 X).app (Opposite.op ⦋0⦌)
    ((coreSConstruction 0 X.carrier).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op
      ⟨z, _⟩) = _
  have he : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op =
      𝟙 (Opposite.op ⦋0⦌) := Subsingleton.elim _ _
  rw [he, CategoryTheory.Functor.map_id]
  exact h

/-- 元の object S の辺は、境界商で境界定数な一次単体となる。 -/
def objectBoundaryEdge (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    (((boundaryKanRealizationFunctor 0).obj X).right).PtSimplex 1
      ((boundaryKanRealizationFunctor 0).obj X).basepoint where
  map := SSet.yonedaEquiv.symm e ≫ objectBoundaryKanComparison X
  comm := by
    apply boundary.hom_ext
    intro i
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply SSet.yonedaEquiv.injective
    rw [← Category.assoc, SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, SSet.yonedaEquiv_const]
    exact objectBoundaryKanComparison_vertex X _

/-- 元の object S₂ そのものが三辺の乗法の証拠を与える。 -/
def objectBoundaryTriangle (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    PtSimplex.MulStruct
      (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 2 q))
      (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 0 q))
      (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 1 q)) (0 : Fin 1) where
  map := SSet.yonedaEquiv.symm q ≫ objectBoundaryKanComparison X
  δ_castSucc_castSucc_map := by
    change stdSimplex.δ (0 : Fin 3) ≫ _ ≫ _ = _
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl
  δ_succ_castSucc_map := by
    change stdSimplex.δ (1 : Fin 3) ≫ _ ≫ _ = _
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl
  δ_succ_succ_map := by
    change stdSimplex.δ (2 : Fin 3) ≫ _ ≫ _ = _
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl
  δ_map_of_lt j hj := by simp at hj
  δ_map_of_gt j hj := by
    have hj' : (2 : Fin 3) < j := hj
    omega

/-- 元の S₂ の三辺は、一重 S の実際の基本群で三角形の積の関係を満たす。 -/
lemma objectBoundaryTriangle_mul (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 2 q)) *
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 0 q)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X ((objectSConstruction X.carrier).δ 1 q)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (objectBoundaryTriangle X q)

end SerrePositivity.KST.SConstruction
