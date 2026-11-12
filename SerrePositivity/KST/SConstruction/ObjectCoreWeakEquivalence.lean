module
public import SerrePositivity.KST.SConstruction.ConstantFamilySwap

/-! # 元の object S から core S 実現への比較の弱同値
概要：安定な quasicategory の元の object/core 比較は anodyne 局所化で同型。
方針：D(m,w) の定数包含を行の同型で照合し、行ごとの弱同値を転置した対角へ移す。
規約：object/core 比較の弱同値を入力にしない。使われ方：Fiore–Pieper Proposition 4.27。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：core S の各転置行への object 包含は局所化で同型。
方針：定数図式の object S の弱同値と行の同型を元の射に照合する。
規約：全ての行の次数に成立。使われ方：対角の弱同値の入力。 -/
lemma objectRowInclusion_coreS_localized_isIso (m : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectRowInclusion (simplicialCoreSConstruction X.carrier) (Opposite.op ⦋m⦌))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have : IsIso (Q.map (objectSConstructionFunctor.map (equivalenceDiagramStableConstant m X))) :=
    equivalenceDiagramStableConstant_objectS_localized_isIso m X
  have h : IsIso (Q.map (objectSConstructionFunctor.map (equivalenceDiagramStableConstant m X) ≫
      (objectCoreRowIso m X.carrier).hom)) := by
    rw [Q.map_comp]
    infer_instance
  rw [objectCoreRowIso_constant, Q.map_comp] at h
  exact (isIso_comp_left_iff _ _).mp h

/-- 概要：core S の object から対角への元の包含は局所化で同型。
方針：転置した行の弱同値を対角に移し、転置前後の対角の同型を合成する。
規約：対角の Kan 性は要求しない。使われ方：元の object/core 比較の証明。 -/
lemma diagonalObjectInclusion_coreS_localized_isIso (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : IsIso (AnodyneHomotopy.anodyneQ.map
      (diagonalObjectInclusion (simplicialCoreSConstruction C))) := by
  let X : StableModel.{u} := ⟨C⟩
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hi (m : SimplexCategoryᵒᵖ) : IsIso
      (Q.map ((objectRowsInclusion (simplicialCoreSConstruction C)).app m)) :=
    objectRowInclusion_coreS_localized_isIso m.unop.len X
  have : IsIso (Q.map (simplicialDiagonalFunctor.map
      (objectRowsInclusion (simplicialCoreSConstruction C)))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map _ hi
  rw [← objectRowsInclusion_diagonal, Q.map_comp, Q.map_comp]
  infer_instance

/-- 概要：安定な quasicategory の object S から core S の対角実現への元の射は弱同値。
方針：core の全頂点性の同型と、行から対角へ移した弱同値を合成する。
規約：追加の比較仮定は不要。使われ方：McCarthy の object 加法性の core 実現への移送。 -/
lemma objectToCoreSRealization_localized_isIso (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectToCoreSRealization C)) := by
  have := diagonalObjectInclusion_coreS_localized_isIso C
  rw [objectToCoreSRealization, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
