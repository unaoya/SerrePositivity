module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeStability
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveProjections
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedQuasiEquivalence
public import SerrePositivity.KST.SConstruction.DGKUniverseQuasiEquivalence
/-!
概要：対象宇宙の異なる元 dg gluing の二射影は、共通宇宙で完全である。
方針：対象ラベルを共通宇宙へ上げ、公開済みの dg 関手の完全性を実 nerve 同型で戻す。
規約：元の全 Hom 作用と二射影を保持する。模型圏構造の仮定を追加しない。
使われ方：安定 lax pullback との比較と半直交分解の射影に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
lemma dgGluingUniverseNerveMap_isExactFunctor (F : DGFunctor R C D)
    [IsDGPretriangulated R C] [IsDGPretriangulated R D] :
    IsExactFunctor (dgGluingUniverseNerveMap.{u,v,w,max u r} F) := by
  let := isDGPretriangulated_of_quasiEquivalence R (DGUniverseLift.{v,max u w r} C) C
    (dgUniverseLiftDown R C)
    (KST.SConstruction.dgKUniverseLiftDown_quasiEquivalence R C)
  let := isDGPretriangulated_of_quasiEquivalence R (DGUniverseLift.{w,max u v r} D) D
    (dgUniverseLiftDown R D)
    (KST.SConstruction.dgKUniverseLiftDown_quasiEquivalence R D)
  let := dgPretriangulatedFunctor_isExactFunctor R
    (DGUniverseLift.{v,max u w r} C) (DGUniverseLift.{w,max u v r} D)
    (dgUniverseLiftFunctor F)
  let := isExactFunctor_of_isQCatEquivalence
    (qCatEquivalenceOfIso (dgNerveUniverseLiftIso.{u,v,max u w r} R C)).isQCatEquivalence
  let := isExactFunctor_of_isQCatEquivalence
    (qCatEquivalenceOfIso (dgNerveUniverseLiftIso.{u,w,max u v r} R D).symm).isQCatEquivalence
  have he : (dgNerveUniverseLiftIso.{u,v,max u w r} R C).hom ≫
      dgNerve.map (dgUniverseLiftFunctor.{u,v,w,max u w r,max u v r} F) ≫
      (dgNerveUniverseLiftIso.{u,w,max u v r} R D).inv =
      dgGluingUniverseNerveMap.{u,v,w,max u r} F := by
    ext n s
    apply ULift.ext
    apply Simplex.ext
    rfl
  rw [← he]
  infer_instance

variable (R) (C) (D) (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingUniverseLeftNerve_isExactFunctor :
    IsExactFunctor (dgGluingUniverseLeftNerve R C D M) := by
  let := hC
  let := hD
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact dgGluingUniverseNerveMap_isExactFunctor.{u,max u v w,v,max (u + 1) v w}
    (dgGluingLeft R C D M)
lemma dgGluingUniverseRightNerve_isExactFunctor :
    IsExactFunctor (dgGluingUniverseRightNerve R C D M) := by
  let := hC
  let := hD
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact dgGluingUniverseNerveMap_isExactFunctor.{u,max u v w,w,max (u + 1) v w}
    (dgGluingRight R C D M)
end SerrePositivity.InfinityCategories
