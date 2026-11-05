module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.CoslicePointHomNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceFiberVertices

/-! # pointed space の同じ全パラメーター族は、元の点の射の自然性を全射で保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 元の pointed-space 頂点を、その同じ射影先の実 fiber 点として読む。 -/
def pointedVertexFiberPoint (s : PointedSpaceInfinity.{u} _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) s)) _⦋0⦌ :=
  ⟨s, (pinchedConstant_zero _).symm⟩

/-- 元の pointed-space 頂点が指定する、同じ一点空間からの射。 -/
def pointedVertexPointHom (s : PointedSpaceInfinity.{u} _⦋0⦌) :
    HomotopyCategory.mk pointSpaceVertex ⟶ HomotopyCategory.mk
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) s) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint s)

/-- 全パラメーター族内の元の射は、同じ点の射と同じ底の射との合成式を保つ。 -/
theorem pointedFamilyPointHom_naturality {K : SSet.{u + 1}}
    (H : K ⟶ PointedSpaceInfinity.{u}) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫
      (hoFunctor.map (H ≫ pointedSpaceProjection)).toFunctor.map m =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) w) := by
  have he := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom_comp_projection
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) v))
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) w))
    ((hoFunctor.map H).toFunctor.map m)
  have hp : _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberHomProjection
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) v))
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint (H.app (Opposite.op ⦋0⦌) w))
      ((hoFunctor.map H).toFunctor.map m) =
      (hoFunctor.map (H ≫ pointedSpaceProjection)).toFunctor.map m := by
    change 𝟙 (HomotopyCategory.mk
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) v))) ≫
      (hoFunctor.map pointedSpaceProjection).toFunctor.map ((hoFunctor.map H).toFunctor.map m) ≫
      𝟙 (HomotopyCategory.mk
        (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) w))) = _
    calc
      _ = (hoFunctor.map pointedSpaceProjection).toFunctor.map
          ((hoFunctor.map H).toFunctor.map m) :=
        (Category.id_comp _).trans (Category.comp_id _)
      _ = _ := by
        have hf : (hoFunctor.map H).toFunctor ⋙
            (hoFunctor.map pointedSpaceProjection).toFunctor =
            (hoFunctor.map (H ≫ pointedSpaceProjection)).toFunctor := by
          rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
        simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
          CategoryTheory.Functor.congr_hom hf m
  rw [hp] at he
  exact he

/-- 同じ全 pointed 族の射影先を、指定した同じ底の族へ表示変更する元の値同型。 -/
def pointedFamilyProjectionValueIso {K : SSet.{u + 1}} (H : K ⟶ PointedSpaceInfinity.{u})
    (J : K ⟶ SpaceInfinity.{u}) (h : H ≫ pointedSpaceProjection = J) (v : K _⦋0⦌) :
    VertexIso (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (H.app (Opposite.op ⦋0⦌) v))
      (J.app (Opposite.op ⦋0⦌) v) :=
  eqToIso (congrArg HomotopyCategory.mk (congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) h))

/-- 同じ底の族への表示変更は、その元の射の作用を保持する。 -/
theorem pointedFamilyProjectionValueIso_map {K : SSet.{u + 1}}
    (H : K ⟶ PointedSpaceInfinity.{u}) (J : K ⟶ SpaceInfinity.{u})
    (h : H ≫ pointedSpaceProjection = J) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J h v).hom ≫ (hoFunctor.map J).toFunctor.map m ≫
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J h w).inv =
      (hoFunctor.map (H ≫ pointedSpaceProjection)).toFunctor.map m := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- 指定した同じ底の全族で表示しても、元の点の射の自然性を保つ。 -/
theorem pointedFamilyPointHom_naturality_over {K : SSet.{u + 1}}
    (H : K ⟶ PointedSpaceInfinity.{u}) (J : K ⟶ SpaceInfinity.{u})
    (h : H ≫ pointedSpaceProjection = J) {v w : K _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J h v).hom ≫ (hoFunctor.map J).toFunctor.map m ≫
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J h w).inv =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) w) :=
  (congrArg (fun n => _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) v) ≫ n)
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso_map H J h m)).trans (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyPointHom_naturality H m)

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFamilyPointHom_naturality := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyPointHom_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFamilyPointHom_naturality_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyPointHom_naturality_over

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFamilyProjectionValueIso := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFamilyProjectionValueIso_map := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso_map

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedVertexFiberPoint := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedVertexPointHom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFamilyProjectionValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedVertexFiberPoint._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint._proof_1
