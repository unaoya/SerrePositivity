module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CoslicePointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices

/-! # pointed space の同じ全パラメーター族は、元の点の射の自然性を全射で保つ

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration

/-- 元の pointed-space 頂点を、その同じ射影先の実 fiber 点として読む。 -/
def pointedVertexFiberPoint (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) s)) _⦋0⦌ :=
  ⟨s, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 元の pointed-space 頂点が指定する、同じ一点空間からの射。 -/
def pointedVertexPointHom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} _⦋0⦌) :
    HomotopyCategory.mk _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex ⟶ HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint s)

/-- 全パラメーター族内の元の射は、同じ点の射と同じ底の射との合成式を保つ。 -/
theorem pointedFamilyPointHom_naturality {K : SSet.{u + 1}}
    (H : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫
      (hoFunctor.map (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)).toFunctor.map m =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) w) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberPointHom_comp_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) v))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) w))
    ((hoFunctor.map H).toFunctor.map m)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberHomProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) v))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) w))
      ((hoFunctor.map H).toFunctor.map m) =
      (hoFunctor.map (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)).toFunctor.map m := by
    change 𝟙 (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) v))) ≫
      (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection).toFunctor.map ((hoFunctor.map H).toFunctor.map m) ≫
      𝟙 (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) w))) = _
    calc
      _ = (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection).toFunctor.map
          ((hoFunctor.map H).toFunctor.map m) :=
        (Category.id_comp _).trans (Category.comp_id _)
      _ = _ := by
        have hf : (hoFunctor.map H).toFunctor ⋙
            (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection).toFunctor =
            (hoFunctor.map (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)).toFunctor := by
          rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
        simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
          CategoryTheory.Functor.congr_hom hf m
  rw [hp] at he
  exact he

/-- 同じ全 pointed 族の射影先を、指定した同じ底の族へ表示変更する元の値同型。 -/
def pointedFamilyProjectionValueIso {K : SSet.{u + 1}} (H : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u})
    (J : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (h : H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = J) (v : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) v))
      (J.app (Opposite.op ⦋0⦌) v) :=
  eqToIso (congrArg HomotopyCategory.mk (congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) h))

/-- 同じ底の族への表示変更は、その元の射の作用を保持する。 -/
theorem pointedFamilyProjectionValueIso_map {K : SSet.{u + 1}}
    (H : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}) (J : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h : H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = J) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyProjectionValueIso H J h v).hom ≫ (hoFunctor.map J).toFunctor.map m ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyProjectionValueIso H J h w).inv =
      (hoFunctor.map (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)).toFunctor.map m := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- 指定した同じ底の全族で表示しても、元の点の射の自然性を保つ。 -/
theorem pointedFamilyPointHom_naturality_over {K : SSet.{u + 1}}
    (H : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}) (J : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h : H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = J) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyProjectionValueIso H J h v).hom ≫ (hoFunctor.map J).toFunctor.map m ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyProjectionValueIso H J h w).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) w) :=
  (congrArg (fun n => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫ n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyProjectionValueIso_map H J h m)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedFamilyPointHom_naturality H m)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
