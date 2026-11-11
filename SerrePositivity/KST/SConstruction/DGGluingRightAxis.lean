module
public import SerrePositivity.KST.SConstruction.DGClosedZeroHom
public import SerrePositivity.KST.SConstruction.DGStrictGluingFunctor

/-! # 元の閉零対象を用いる実 dg gluing の右軸包含
概要：元の d を同じ (0,d,0) へ送る全 Hom の実 dg 関手を構成する。
方針：閉零対象の定数関手と恒等関手を、代表加群の Hom 零性で gluing へ束ねる。
規約：左成分の閉零性を入力する。使われ方：指定生成元の実包含と商の右脚。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))

/-- 元の閉零対象と同じ右成分・零比較を保持する実 gluing 対象。 -/
def dgGluingRightAxisObject (d : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M := ⟨z, d, 0⟩

/-- 元の d を同じ (0,d,0) へ送る、全 Hom を持つ実 dg 包含。 -/
def dgGluingRightAxis : DGFunctor R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  dgStrictGluingFunctor R C D M (dgClosedZeroFunctor R z hz D) (DGFunctor.id D)
    (fun _ => 0) (fun _ y => (dgRepresentableClosedZeroHom R z hz (M.rightAt y)).eq_of_tgt _ _)

/-- 同じ右軸包含は、元の対象 (0,d,0) を厳密に回収する。 -/
lemma dgGluingRightAxis_obj (d : D) :
    (dgGluingRightAxis R C D M z hz).obj d = dgGluingRightAxisObject R C D M z d := rfl

/-- 同じ右射影との合成は、元の右圏の恒等 dg 関手そのもの。 -/
lemma dgGluingRightAxis_right :
    (dgGluingRightAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) = DGFunctor.id D :=
  dgStrictGluingFunctor_right R C D M (dgClosedZeroFunctor R z hz D) (DGFunctor.id D)
    (fun _ => 0) (fun _ y => (dgRepresentableClosedZeroHom R z hz (M.rightAt y)).eq_of_tgt _ _)

/-- 同じ左射影との合成は、元の閉零対象値の実 dg 零関手。 -/
lemma dgGluingRightAxis_left :
    (dgGluingRightAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) =
      dgClosedZeroFunctor R z hz D :=
  dgStrictGluingFunctor_left R C D M (dgClosedZeroFunctor R z hz D) (DGFunctor.id D)
    (fun _ => 0) (fun _ y => (dgRepresentableClosedZeroHom R z hz (M.rightAt y)).eq_of_tgt _ _)

end SerrePositivity.KST.SConstruction
