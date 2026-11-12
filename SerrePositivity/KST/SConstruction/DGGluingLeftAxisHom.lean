module
public import SerrePositivity.KST.SConstruction.DGGluingLeftAxis
public import SerrePositivity.KST.SConstruction.DGCommaZeroReplacementProjection
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 実左軸包含の全 Hom 同型
概要：元の左軸 (c,0,0) 間の全 Hom は、同じ左圏の Hom と実鎖同型で一致する。
方針：代表加群表示へ移し、比較側の実零性から入力射影の同型を得る。
規約：Hom 準同型だけでなく元の射影・包含を保持。使われ方：生成元と商の右脚。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma postIsoInverseCancel {V : Type*} [Category V] {A B K : V}
    (f : K ⟶ B) (e : A ≅ B) : (f ≫ e.inv) ≫ e.hom = f := by
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

private lemma dgFunctorMapOfEq {R : Type u} [CommRing R]
    {B : Type*} {C : Type*} [DGCategory R B] [DGCategory R C]
    (H J : DGFunctor R B C) (he : H = J) (ho : ∀ x, H.obj x = J.obj x) (x y : B) :
    H.map x y ≫ eqToHom (congrArg₂ (homObject R C) (ho x) (ho y)) = J.map x y := by
  cases he
  simp only [eqToHom_refl, Category.comp_id]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : D) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))

/-- 同じ実左軸間の全 Hom を、元の左射影そのものを持つ鎖同型で比較する。 -/
def dgGluingLeftAxisHomIso (d e : C) :
    homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e) ≅
    homObject R C d e :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M
    (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e)) ≪≫
    (dgCommaZeroReplacementIso R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingLeftAxisObject R C D M z d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingLeftAxisObject R C D M z e))
      (dgHom_isZero_of_closed_zero_target R z hz z)
      (dgBimoduleClosedZero_hom R C D M z hz (representable R d)))) ≪≫
    dgYonedaIso R d (representable R e)

/-- 同じ全 Hom 同型の順射は、元の実左 Hom 射影そのもの。 -/
lemma dgGluingLeftAxisHomIso_hom (d e : C) :
    (dgGluingLeftAxisHomIso R C D M z hz d e).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M
        (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e) := by
  have hh := congrArg (fun k => k ≫ (dgYonedaIso R d (representable R e)).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_left R C D M
      (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e))
  exact hh.trans (postIsoInverseCancel
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M
      (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e))
    (dgYonedaIso R d (representable R e)))

/-- 元の実左軸包含の Hom 作用と元の左射影は、厳密に恒等写像へ合成する。 -/
lemma dgGluingLeftAxis_map_left (d e : C) :
    (dgGluingLeftAxis R C D M z hz).map d e ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M
      (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e) =
      𝟙 (homObject R C d e) := by
  have hh := dgFunctorMapOfEq
    ((dgGluingLeftAxis R C D M z hz).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)) (DGFunctor.id C)
    (dgGluingLeftAxis_left R C D M z hz) (fun _ => rfl) d e
  change ((dgGluingLeftAxis R C D M z hz).map d e ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M
      (dgGluingLeftAxisObject R C D M z d) (dgGluingLeftAxisObject R C D M z e)) ≫
        𝟙 _ = 𝟙 _ at hh
  rw [Category.comp_id] at hh
  exact hh

/-- 元の実左軸包含の Hom 作用は、同じ左 Hom 射影同型の逆そのもの。 -/
lemma dgGluingLeftAxis_map (d e : C) :
    (dgGluingLeftAxis R C D M z hz).map d e =
      (dgGluingLeftAxisHomIso R C D M z hz d e).inv := by
  apply (cancel_mono (dgGluingLeftAxisHomIso R C D M z hz d e).hom).mp
  exact ((congrArg (fun k => (dgGluingLeftAxis R C D M z hz).map d e ≫ k)
    (dgGluingLeftAxisHomIso_hom R C D M z hz d e)).trans
      (dgGluingLeftAxis_map_left R C D M z hz d e)).trans
        (dgGluingLeftAxisHomIso R C D M z hz d e).inv_hom_id.symm

/-- 同じ実左軸包含は、全 Hom 複体で実同型を誘導する。 -/
lemma dgGluingLeftAxis_map_isIso (d e : C) :
    IsIso ((dgGluingLeftAxis R C D M z hz).map d e) := by
  rw [dgGluingLeftAxis_map]
  exact ⟨⟨(dgGluingLeftAxisHomIso R C D M z hz d e).hom,
    (dgGluingLeftAxisHomIso R C D M z hz d e).inv_hom_id,
    (dgGluingLeftAxisHomIso R C D M z hz d e).hom_inv_id⟩⟩

/-- 同じ実左軸包含は、全 Hom 複体で準同型を誘導する。 -/
lemma dgGluingLeftAxis_homQuasiIso : HomQuasiIso (dgGluingLeftAxis R C D M z hz) := by
  intro d e
  have := dgGluingLeftAxis_map_isIso R C D M z hz d e
  infer_instance

end SerrePositivity.KST.SConstruction
