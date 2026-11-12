module
public import SerrePositivity.KST.SConstruction.DGGluingRightAxis
public import SerrePositivity.KST.SConstruction.DGCommaZeroSourceProjection
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 実右軸包含の全 Hom 同型
概要：元の右軸 (0,d,0) 間の全 Hom は、同じ右圏の Hom と実鎖同型で一致する。
方針：代表加群表示へ移し、比較側の実零性から入力射影の同型を得る。
規約：Hom 準同型だけでなく元の射影・包含を保持。使われ方：生成元と商の右脚。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma dgFunctorMapOfEq {R : Type u} [CommRing R]
    {B : Type*} {C : Type*} [DGCategory R B] [DGCategory R C]
    (H J : DGFunctor R B C) (he : H = J) (ho : ∀ x, H.obj x = J.obj x) (x y : B) :
    H.map x y ≫ eqToHom (congrArg₂ (homObject R C) (ho x) (ho y)) = J.map x y := by
  cases he
  simp only [eqToHom_refl, Category.comp_id]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))

/-- 同じ実右軸間の全 Hom を、元の右射影そのものを持つ鎖同型で比較する。 -/
def dgGluingRightAxisHomIso (d e : D) :
    homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (dgGluingRightAxisObject R C D M z d) (dgGluingRightAxisObject R C D M z e) ≅
    homObject R D d e :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M
    (dgGluingRightAxisObject R C D M z d) (dgGluingRightAxisObject R C D M z e)) ≪≫
  (dgCommaZeroSourceIso R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z e))
    (dgRepresentableClosedZeroHom R z hz (representable R z))
    (dgRepresentableClosedZeroHom R z hz (M.rightAt e)))

/-- 同じ全 Hom 同型の順射は、元の実右 Hom 射影そのもの。 -/
lemma dgGluingRightAxisHomIso_hom (d e : D) :
    (dgGluingRightAxisHomIso R C D M z hz d e).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M
        (dgGluingRightAxisObject R C D M z d) (dgGluingRightAxisObject R C D M z e) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_right R C D M _ _

/-- 元の実右軸包含の Hom 作用と元の右射影は、厳密に恒等写像へ合成する。 -/
lemma dgGluingRightAxis_map_right (d e : D) :
    (dgGluingRightAxis R C D M z hz).map d e ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M
      (dgGluingRightAxisObject R C D M z d) (dgGluingRightAxisObject R C D M z e) =
      𝟙 (homObject R D d e) := by
  have hh := dgFunctorMapOfEq
    ((dgGluingRightAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)) (DGFunctor.id D)
    (dgGluingRightAxis_right R C D M z hz) (fun _ => rfl) d e
  change ((dgGluingRightAxis R C D M z hz).map d e ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).map _ _) ≫ 𝟙 _ = 𝟙 _ at hh
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map] at hh
  exact hh

/-- 元の実右軸包含の Hom 作用は、同じ右 Hom 射影同型の逆そのもの。 -/
lemma dgGluingRightAxis_map (d e : D) :
    (dgGluingRightAxis R C D M z hz).map d e =
      (dgGluingRightAxisHomIso R C D M z hz d e).inv := by
  apply (cancel_mono (dgGluingRightAxisHomIso R C D M z hz d e).hom).mp
  exact ((congrArg (fun k => (dgGluingRightAxis R C D M z hz).map d e ≫ k)
    (dgGluingRightAxisHomIso_hom R C D M z hz d e)).trans
      (dgGluingRightAxis_map_right R C D M z hz d e)).trans
        (dgGluingRightAxisHomIso R C D M z hz d e).inv_hom_id.symm

/-- 同じ実右軸包含は、全 Hom 複体で実同型を誘導する。 -/
lemma dgGluingRightAxis_map_isIso (d e : D) :
    IsIso ((dgGluingRightAxis R C D M z hz).map d e) := by
  rw [dgGluingRightAxis_map]
  exact ⟨⟨(dgGluingRightAxisHomIso R C D M z hz d e).hom,
    (dgGluingRightAxisHomIso R C D M z hz d e).inv_hom_id,
    (dgGluingRightAxisHomIso R C D M z hz d e).hom_inv_id⟩⟩

/-- 同じ実右軸包含は、全 Hom 複体で準同型を誘導する。 -/
lemma dgGluingRightAxis_homQuasiIso : HomQuasiIso (dgGluingRightAxis R C D M z hz) := by
  intro d e
  have := dgGluingRightAxis_map_isIso R C D M z hz d e
  infer_instance

end SerrePositivity.KST.SConstruction
