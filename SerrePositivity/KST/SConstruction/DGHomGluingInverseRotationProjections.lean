module
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotation

/-!
概要：実逆回転の Hom gluing 関手の両射影は元の実二成分を厳密に保持する。
方針：抽象恒等 Hom gluing 関手の同じ全 dg 回収式を適用する。
規約：元二重 shift と全 cone を保持。使われ方：共通 LT 実長方形の二脚回収。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "T" => DGHomGluingLoopConeBase R C D E p q

/-- 概要：実逆回転の左射影は同じ実逆 shift cone 関手。
方針：元恒等 Hom gluing 関手の回収を使う。
規約：元全 Hom と対象を保持。使われ方：LT 実中央比較の左脚。 -/
lemma dgHomGluingInverseRotationFunctor_left :
    (dgHomGluingInverseRotationFunctor R C D E p q).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (T) (T)
        (dgHomGluingBimodule R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))) =
      dgHomGluingLoopConeSmall R C D E p q :=
  dgIdentityHomGluingFunctor_left R (T)
    (dgHomGluingLoopConeSmall R C D E p q) (dgHomGluingLoopConeShiftedTarget R C D E p q)
    (dgHomGluingInverseRotationMap R C D E p q)
    (dgHomGluingInverseRotationMap_hom_naturality R C D E p q)

/-- 概要：実逆回転の右射影は同じ元左対象の指定二重 shift 関手。
方針：元恒等 Hom gluing 関手の回収を使う。
規約：元全 Hom と対象を保持。使われ方：LT 実中央比較の右脚。 -/
lemma dgHomGluingInverseRotationFunctor_right :
    (dgHomGluingInverseRotationFunctor R C D E p q).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (T) (T)
        (dgHomGluingBimodule R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))) =
      dgHomGluingLoopConeShiftedTarget R C D E p q :=
  dgIdentityHomGluingFunctor_right R (T)
    (dgHomGluingLoopConeSmall R C D E p q) (dgHomGluingLoopConeShiftedTarget R C D E p q)
    (dgHomGluingInverseRotationMap R C D E p q)
    (dgHomGluingInverseRotationMap_hom_naturality R C D E p q)
end SerrePositivity.KST.SConstruction
