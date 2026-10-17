module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractSingle

/-! # 逆回転三角形から有限射影代表を戻す

single→X→Kの両端が有限射影で表されるとき、実際のchain mapのconeでXを表す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedTriangle_middle_finiteRange
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (F : ModuleCat.{u} A) [Module.Finite A F] [Module.Projective A F]
    (K : Complex A) (hK : strictlyPerfectComplex A K) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE (b - 1)] (hab : a ≤ b)
    (eF : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ≅ T.obj₁)
    (eK : DerivedCategory.Q.obj K ≅ T.obj₃) :
    ∃ L : Complex A, strictlyPerfectComplex A L ∧ L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty (DerivedCategory.Q.obj L ≅ T.obj₂) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) b).obj F
  let K' := K⟦(-1 : ℤ)⟧
  have hK' : strictlyPerfectComplex A K' := strictlyPerfectComplex_shift hK (-1)
  have : K'.IsStrictlyGE (a + 1) := K.isStrictlyGE_shift a (-1) (a + 1) (by omega)
  have : K'.IsStrictlyLE b := K.isStrictlyLE_shift (b - 1) (-1) b (by omega)
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let e₁ : Q.obj K' ≅ T.invRotate.obj₁ := (Q.commShiftIso (-1 : ℤ)).app K ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ)).mapIso eK
  let h := e₁.hom ≫ T.invRotate.mor₁ ≫ eF.inv
  obtain ⟨f, hf⟩ := ringComplexDerived_map_surjective A K' hK' S h
  let C := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let e : C ≅ T.invRotate := isoTriangleOfIso₁₂ C T.invRotate
    (DerivedCategory.mappingCone_triangle_distinguished f) (inv_rot_of_distTriang T hT)
    e₁ eF (by
      change Q.map f ≫ eF.hom = e₁.hom ≫ T.invRotate.mor₁
      rw [hf]
      simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hL : strictlyPerfectComplex A (CochainComplex.mappingCone f) :=
    strictlyPerfectComplex_mappingCone A f hK' (strictlyPerfectComplex_single A F b)
  have hge : (CochainComplex.mappingCone f).IsStrictlyGE a :=
    CochainComplex.isStrictlyGE_mappingCone f (a + 1) b a (by omega) hab
  have hle : (CochainComplex.mappingCone f).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K'.isZero_of_isStrictlyLE b (i + 1) (by omega),
      CochainComplex.isZero_of_isStrictlyLE S b i hi⟩
  exact ⟨_, hL, hge, hle, ⟨Triangle.π₃.mapIso e⟩⟩

end SerrePositivity.DifferentialGraded
