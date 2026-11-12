module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomMap
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeIdentity
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveUnit

/-! # 元の全 Hom cone 写像の単位保存
概要：元の gluing 単位を、同じ実 Perf cone の単位へ送ることを証明する。
方針：元の左右射影・Yoneda の単位保存と第三成分の零性を合成する。
規約：対象族と元の全 Hom 写像を保持。使われ方：実 dg cone 関手の包装。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 左の実 Hom 成分は元の gluing 単位を元の左表現可能加群の単位に送る。 -/
lemma dgHomGluingConeLeftMap_unit :
    (dgHomGluingConeLeftMap R C D E p q X X).f 0 (unitElement R X).val =
      (unitElement R (representable R (p.obj X.left))).val :=
  DGFunctor.map_unitElement R
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p).comp
      (dgYoneda R E)) X

/-- 右の実 Hom 成分も元の右表現可能加群の単位を回収する。 -/
lemma dgHomGluingConeRightMap_unit :
    (dgHomGluingConeRightMap R C D E p q X X).f 0 (unitElement R X).val =
      (unitElement R (representable R (q.obj X.right))).val := by
  have h := DGFunctor.map_unitElement R
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).comp q).comp
      (dgYoneda R E)) X
  change ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).map X X ≫
    q.map X.right X.right) ≫ (dgYoneda R E).map _ _).f 0
      (unitElement R X).val) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at h
  exact h

/-- 第三成分の Yoneda 像も元の gluing 単位で零になる。 -/
lemma dgHomGluingConePrimitive_unit :
    (dgHomGluingConePrimitive R C D E p q X X).v 0 (-1) (by omega)
      (unitElement R X).val = 0 := by
  rw [dgHomGluingConePrimitive_apply, dgHomGluingUnit_primitive]
  exact map_zero (((dgYoneda R E).map (p.obj X.left) (q.obj X.right)).f (-1)).hom

/-- 元の実 Hom 鎖写像は元の gluing 単位を同じ実 Perf cone の単位に送る。 -/
lemma dgHomGluingConeHomMap_unit :
    (dgHomGluingConeHomMap R C D E p q X X).f 0 (unitElement R X).val =
      (unitElement R (dgHomGluingTargetCone R C D E p q X)).val := by
  erw [dgHomGluingConeHomMap_apply, dgHomGluingConeLeftMap_unit,
    dgHomGluingConeRightMap_unit, dgHomGluingConePrimitive_unit]
  exact dgGluingModuleConeElement_identity R E _

end SerrePositivity.KST.SConstruction
