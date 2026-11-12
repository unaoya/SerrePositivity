module
public import SerrePositivity.KST.SConstruction.DGBimoduleClosedZero
public import SerrePositivity.KST.SConstruction.DGStrictGluingFunctor

/-! # 元の閉零右対象を用いる実 dg gluing の左軸包含
概要：元の c を同じ (c,0,0) へ送る全 Hom の実 dg 関手を構成する。
方針：元の恒等関手と閉零右対象の定数関手を、双加群の Hom 零性で束ねる。
規約：元の右対象の閉零性を入力する。使われ方：元の対象の二軸分解。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : D) (hz : IsZero (ForgetEnrichment.of (Complex R) z))

/-- 元の左成分と同じ閉零右対象・零比較を持つ実 gluing 対象。 -/
def dgGluingLeftAxisObject (c : C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M := ⟨c, z, 0⟩

/-- 元の c を同じ (c,0,0) へ送る、全 Hom を持つ実 dg 包含。 -/
def dgGluingLeftAxis : DGFunctor R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  dgStrictGluingFunctor R C D M (DGFunctor.id C) (dgClosedZeroFunctor R z hz C)
    (fun _ => 0) (fun x _ => (dgBimoduleClosedZero_hom R C D M z hz
      (representable R x)).eq_of_tgt _ _)

/-- 同じ左軸包含は、元の対象 (c,0,0) を厳密に回収する。 -/
lemma dgGluingLeftAxis_obj (c : C) :
    (dgGluingLeftAxis R C D M z hz).obj c = dgGluingLeftAxisObject R C D M z c := rfl

/-- 同じ左射影との合成は、元の左圏の恒等 dg 関手そのもの。 -/
lemma dgGluingLeftAxis_left :
    (dgGluingLeftAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M) = DGFunctor.id C :=
  dgStrictGluingFunctor_left R C D M (DGFunctor.id C) (dgClosedZeroFunctor R z hz C)
    (fun _ => 0) (fun x _ => (dgBimoduleClosedZero_hom R C D M z hz
      (representable R x)).eq_of_tgt _ _)

/-- 同じ右射影との合成は、元の閉零右対象値の実 dg 零関手。 -/
lemma dgGluingLeftAxis_right :
    (dgGluingLeftAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M) =
      dgClosedZeroFunctor R z hz C :=
  dgStrictGluingFunctor_right R C D M (DGFunctor.id C) (dgClosedZeroFunctor R z hz C)
    (fun _ => 0) (fun x _ => (dgBimoduleClosedZero_hom R C D M z hz
      (representable R x)).eq_of_tgt _ _)

end SerrePositivity.KST.SConstruction
