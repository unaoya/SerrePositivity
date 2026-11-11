module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronLongFaces

/-!
概要：三単体の端の射による path の左右合成。
方針：四頂点の path の合成を有限集合の和集合として計算する。
規約：両端と精密化の一次単体を厳密に保つ。
使われ方：coherent 三単体の四面の合成則。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：始端の固定射 01 の path。
方針：面 013 の最初の辺を取る。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronPath01 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 1) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
    ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (1 : Fin 3)⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath01
/-- 概要：終端の固定射 23 の path。
方針：面 023 の最後の辺を取る。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronPath23 :
    SimplicialThickening.Path (ULift.up (2 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  (SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
    ⟨ULift.up (1 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTrianglePath12
/-- 概要：面 123 の長辺への path の写像。
方針：面 δ₀ の順序写像を使う。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronFace123 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      SimplicialThickening.Path (ULift.up (1 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
  SimplicialThickening.functorMap (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap _ _
/-- 概要：面 012 の長辺への path の写像。
方針：面 δ₃ の順序写像を使う。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronFace012 :
    SimplicialThickening.Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 2) :=
  SimplicialThickening.functorMap (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap _ _
/-- 概要：固定した 01 path による前合成。
方針：和集合の包含で射への作用を定める。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronWhisker01 :
    SimplicialThickening.Path (ULift.up (1 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) ⥤
      SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  obj P := (show (⟨ULift.up (0 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
    ⟨ULift.up 1⟩ from coherentTetrahedronPath01) ≫
      (show (⟨ULift.up (1 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
        ⟨ULift.up 3⟩ from P)
  map r := ⟨⟨⟨Set.union_subset_union (Set.Subset.refl _) r.hom.down.down⟩⟩⟩
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
/-- 概要：固定した 23 path による後合成。
方針：和集合の包含で射への作用を定める。
規約：元の path の厳密な等式を使う。
使われ方：四面の指定辺を共通の Hom へ移す。 -/
def coherentTetrahedronWhisker23 :
    SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 2) ⥤
      SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  obj P := (show (⟨ULift.up (0 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
    ⟨ULift.up 2⟩ from P) ≫
      (show (⟨ULift.up (2 : Fin 4)⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ⟶
        ⟨ULift.up 3⟩ from coherentTetrahedronPath23)
  map r := ⟨⟨⟨Set.union_subset_union r.hom.down.down (Set.Subset.refl _)⟩⟩⟩
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
