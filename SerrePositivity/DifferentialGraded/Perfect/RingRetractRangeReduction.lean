module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractTriangle

/-! # 有限射影複体の導来retractを一段短い次数幅へ帰着する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_reduce_range (P : Complex A) (hP : strictlyPerfectComplex A P)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P))
    (hab : a < b) :
    ∃ F : ModuleCat.{u} A, Module.Finite A F ∧ Module.Projective A F ∧
      ∃ T : Triangle (DerivedCategory (ModuleCat.{u} A)), T ∈ distTriang _ ∧
        T.obj₁ = DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ∧
        T.obj₂ = X ∧ ∃ P' : Complex A, strictlyPerfectComplex A P' ∧
          P'.IsStrictlyGE a ∧ P'.IsStrictlyLE (b - 1) ∧
            Nonempty (Retract T.obj₃ (DerivedCategory.Q.obj P')) := by
  obtain ⟨Z, e, _⟩ := ringDerivedRetract_complement A r
  let rZ : Retract Z (DerivedCategory.Q.obj P) :=
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd] }
  let := (hP.2 b).1
  have hd : P.d b (b + 1) = 0 := (P.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  let : Module.Finite A (H.obj X) := ringDerivedRetract_topHomology_finite_usual A P b hd r
  let : Module.Finite A (H.obj Z) := ringDerivedRetract_topHomology_finite_usual A P b hd rZ
  obtain ⟨m, fx, hx⟩ := ringDerived_exists_finiteFree_homologyCover A X b
  obtain ⟨n, fz, hz⟩ := ringDerived_exists_finiteFree_homologyCover A Z b
  obtain ⟨Y, gx, dx, hT⟩ := distinguished_cocone_triangle fx
  obtain ⟨W, gz, dz, hU⟩ := distinguished_cocone_triangle fz
  let T := Triangle.mk fx gx dx
  let U := Triangle.mk fz gz dz
  let F₀ := ModuleCat.of A (Fin m → A)
  let F₁ := ModuleCat.of A (Fin n → A)
  let F := F₀ ⊞ F₁
  let ef := (ModuleCat.biprodIsoProd F₀ F₁).symm.toLinearEquiv
  let : Module.Finite A F := Module.Finite.equiv ef
  let : Module.Projective A F := Module.Projective.of_equiv' ef
  let S := single (ModuleCat.{u} A) (.up ℤ) b
  let : PreservesBinaryBiproducts S := preservesBinaryBiproducts_of_preservesBiproducts S
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} A)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e₁ : DerivedCategory.Q.obj (S.obj F) ≅ T.obj₁ ⊞ U.obj₁ :=
    DerivedCategory.Q.mapIso (S.mapBiprod F₀ F₁) ≪≫
      DerivedCategory.Q.mapBiprod (S.obj F₀) (S.obj F₁)
  let : Epi (H.map T.mor₁) := hx
  let : Epi (H.map U.mor₁) := hz
  obtain ⟨f, hf, ⟨rY⟩⟩ := ringDerivedTriangle_sum_coneRetract A T U hT hU F P b e₁ e
  let := hf
  obtain ⟨P', hP', hge, hle, i, hi⟩ := ringSingleCoverCone_shorterModel A F P hP a b f hab
  let := hi
  let e' : DerivedCategory.Q.obj P' ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone f) :=
    asIso (DerivedCategory.Q.map i)
  exact ⟨F₀, inferInstance, inferInstance, T, hT, rfl, rfl,
    P', hP', hge, hle, ⟨rY.trans (Retract.ofIso e'.symm)⟩⟩

end SerrePositivity.DifferentialGraded
