module

public import SerrePositivity.KTheory.Adams.KoszulSquareSwap
public import SerrePositivity.PerfectComplex.ConeArrowMap

/-! # Comparing the homogeneous and mapping-cone coordinates of a Koszul square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex MonoidalCategory
variable {R : Type u} [CommRing R]

namespace Adams

lemma scalarTensorDiagonal_unit_inclusion (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (g : ModuleCat.of R R ⟶ Q.X j) :
    scalarTensorDiagonal ≫ ((oneKoszulUnitSelfIso (R := R)).inv ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) =
    g ≫ (cochainTensorLeftUnitor Q).inv.f j := by
  have hi : (cochainTensorLeftUnitor Q).inv.f j =
      (λ_ (Q.X j)).inv ≫ ((oneKoszulUnitSelfIso (R := R)).inv ▷ Q.X j) ≫
        ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) :=
    HomologicalComplex.leftUnitor'_inv Q j
  rw [hi, tensorHom_def']
  change (λ_ (ModuleCat.of R R)).inv ≫ _ ≫ _ = _
  simp only [Category.assoc]
  have hh : (λ_ (ModuleCat.of R R)).inv ≫ (ModuleCat.of R R ◁ g) =
      g ≫ (λ_ (Q.X j)).inv := (leftUnitor_inv_naturality g).symm
  rw [← Category.assoc (λ_ (ModuleCat.of R R)).inv (ModuleCat.of R R ◁ g), hh]
  exact Category.assoc _ _ _


@[reassoc]
lemma scalarTensorDiagonal_unit_unitor (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (g : ModuleCat.of R R ⟶ Q.X j) :
    scalarTensorDiagonal ≫ ((oneKoszulUnitSelfIso (R := R)).inv ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) Q 0 j j (by omega) ≫
      (cochainTensorLeftUnitor Q).hom.f j = g := by
  have h := congrArg (fun f => f.f j) (cochainTensorLeftUnitor Q).inv_hom_id
  calc
    _ = (g ≫ (cochainTensorLeftUnitor Q).inv.f j) ≫
        (cochainTensorLeftUnitor Q).hom.f j := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ (cochainTensorLeftUnitor Q).hom.f j)
          (scalarTensorDiagonal_unit_inclusion Q j g)
    _ = g := by
      rw [Category.assoc, show (cochainTensorLeftUnitor Q).inv.f j ≫
        (cochainTensorLeftUnitor Q).hom.f j = 𝟙 _ from h, Category.comp_id]

@[reassoc]
lemma oneKoszulSquareConeIso_fst (a : R) (n : ℤ) :
    (oneKoszulSquareConeIso a).hom.f n ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v n (n + 1) rfl =
    tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom.f (n + 1) := by
  simp only [oneKoszulSquareConeIso, oneKoszulTensorConeIso, Iso.trans_hom,
    HomologicalComplex.comp_f, homotopyCofiber.mapArrowIso_hom]
  simp only [Category.assoc]
  change _ ≫ (cochainConeArrowMap
    (cochainTensorMap (oneKoszulScalarMap a) (𝟙 (oneKoszulComplex a)))
    (smulId a (oneKoszulComplex a))
    (Arrow.isoMk (cochainTensorLeftUnitor (oneKoszulComplex a))
      (cochainTensorLeftUnitor (oneKoszulComplex a))
      (oneKoszulTensorScalar_unitor a).symm).hom).f n ≫ _ = _
  rw [cochainConeArrowMap_fst, ← Category.assoc]
  rw [show (cochainTensorConeLeft (oneKoszulScalarMap a) (oneKoszulComplex a)).hom.f n ≫
      (mappingCone.fst (cochainTensorMap (oneKoszulScalarMap a)
        (𝟙 (oneKoszulComplex a)))).1.v n (n + 1) rfl =
      tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n from
    tensorConeXIso_hom_fst _ _ n]
  rfl

@[reassoc]
lemma oneKoszulSquareConeIso_snd (a : R) (n : ℤ) :
    (oneKoszulSquareConeIso a).hom.f n ≫
      (mappingCone.snd (smulId a (oneKoszulComplex a))).v n n (by omega) =
    tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom.f n := by
  simp only [oneKoszulSquareConeIso, oneKoszulTensorConeIso, Iso.trans_hom,
    HomologicalComplex.comp_f, homotopyCofiber.mapArrowIso_hom]
  simp only [Category.assoc]
  change _ ≫ (cochainConeArrowMap
    (cochainTensorMap (oneKoszulScalarMap a) (𝟙 (oneKoszulComplex a)))
    (smulId a (oneKoszulComplex a))
    (Arrow.isoMk (cochainTensorLeftUnitor (oneKoszulComplex a))
      (cochainTensorLeftUnitor (oneKoszulComplex a))
      (oneKoszulTensorScalar_unitor a).symm).hom).f n ≫ _ = _
  rw [cochainConeArrowMap_snd, ← Category.assoc]
  rw [show (cochainTensorConeLeft (oneKoszulScalarMap a) (oneKoszulComplex a)).hom.f n ≫
      (mappingCone.snd (cochainTensorMap (oneKoszulScalarMap a)
        (𝟙 (oneKoszulComplex a)))).v n n (by omega) =
      tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n from
    tensorConeXIso_hom_snd _ _ n]
  rfl

@[reassoc]
lemma oneKoszulTensorGenerator_fst (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫
      tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n =
    scalarTensorDiagonal ≫ ((f ≫ (mappingCone.fst (oneKoszulScalarMap a)).1.v
      i (i + 1) rfl) ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) (oneKoszulComplex a)
        (i + 1) j (n + 1) (by omega) := by
  change scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫
    ιTensorObj (mappingCone (oneKoszulScalarMap a)) (oneKoszulComplex a) i j n h ≫
      tensorConeFstX (oneKoszulScalarMap a) (oneKoszulComplex a) n = _
  rw [ι_tensorConeFstX]
  rw [tensorHom_comp_whiskerRight_assoc]

@[reassoc]
lemma oneKoszulTensorGenerator_snd (a : R) (i j n : ℤ) (h : i + j = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j) :
    oneKoszulTensorGenerator a i j n h f g ≫
      tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n =
    scalarTensorDiagonal ≫ ((f ≫ (mappingCone.snd (oneKoszulScalarMap a)).v
      i i (by omega)) ⊗ₘ g) ≫
      ιTensorObj (oneKoszulUnit (R := R)) (oneKoszulComplex a) i j n h := by
  change scalarTensorDiagonal ≫ (f ⊗ₘ g) ≫
    ιTensorObj (mappingCone (oneKoszulScalarMap a)) (oneKoszulComplex a) i j n h ≫
      tensorConeSndX (oneKoszulScalarMap a) (oneKoszulComplex a) n = _
  rw [ι_tensorConeSndX]
  rw [tensorHom_comp_whiskerRight_assoc]

@[reassoc]
lemma oneKoszulSquareBottom_cone (a : R) :
    oneKoszulSquareBottom a ≫ (oneKoszulSquareConeIso a).hom.f 0 =
      oneKoszulSquareConeBottom a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) 0 1 rfl
  · change oneKoszulSquareBottom a ≫ (oneKoszulSquareConeIso a).hom.f 0 ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v 0 (0 + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareBottom,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXZeroIso, oneKoszulSquareConeBottom]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareBottom,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXZeroIso, oneKoszulSquareConeBottom,
      scalarTensorDiagonal_unit_unitor]

@[reassoc]
lemma oneKoszulSquareLeft_cone (a : R) :
    oneKoszulSquareLeft a ≫ (oneKoszulSquareConeIso a).hom.f (-1) =
      oneKoszulSquareConeLeft a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-1) 0 (by omega)
  · change oneKoszulSquareLeft a ≫ (oneKoszulSquareConeIso a).hom.f (-1) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) ((-1) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareLeft,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeLeft,
      scalarTensorDiagonal_unit_unitor]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareLeft,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeLeft]

@[reassoc]
lemma oneKoszulSquareRight_cone (a : R) :
    oneKoszulSquareRight a ≫ (oneKoszulSquareConeIso a).hom.f (-1) =
      oneKoszulSquareConeRight a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-1) 0 (by omega)
  · change oneKoszulSquareRight a ≫ (oneKoszulSquareConeIso a).hom.f (-1) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) ((-1) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareRight,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXZeroIso, oneKoszulSquareConeRight]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareRight,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXZeroIso, oneKoszulSquareConeRight,
      scalarTensorDiagonal_unit_unitor]

@[reassoc]
lemma oneKoszulSquareTop_cone (a : R) :
    oneKoszulSquareTop a ≫ (oneKoszulSquareConeIso a).hom.f (-2) =
      oneKoszulSquareConeTop a := by
  apply mappingCone.ext_to (smulId a (oneKoszulComplex a)) (-2) (-1) (by omega)
  · change oneKoszulSquareTop a ≫ (oneKoszulSquareConeIso a).hom.f (-2) ≫
      (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-2) ((-2) + 1) rfl = _
    rw [oneKoszulSquareConeIso_fst]
    simp [Category.assoc, oneKoszulSquareTop,
      oneKoszulTensorGenerator_fst_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeTop,
      scalarTensorDiagonal_unit_unitor]
  · simp [Category.assoc, oneKoszulSquareConeIso_snd, oneKoszulSquareTop,
      oneKoszulTensorGenerator_snd_assoc, oneKoszulXNegOneIso, oneKoszulSquareConeTop]

lemma oneKoszulSquareLeft_d (a : R) :
    oneKoszulSquareLeft a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulSquareBottom a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f 0) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ 0).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f 0)).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-1) 0,
    ← Category.assoc, oneKoszulSquareLeft_cone, oneKoszulSquareConeLeft_d,
    Linear.smul_comp, oneKoszulSquareBottom_cone]

lemma oneKoszulSquareRight_d (a : R) :
    oneKoszulSquareRight a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulSquareBottom a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f 0) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ 0).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f 0)).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-1) 0,
    ← Category.assoc, oneKoszulSquareRight_cone, oneKoszulSquareConeRight_d,
    Linear.smul_comp, oneKoszulSquareBottom_cone]

lemma oneKoszulSquareTop_d (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquare (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulSquareRight a - a • oneKoszulSquareLeft a := by
  have : IsIso ((oneKoszulSquareConeIso a).hom.f (-1)) :=
    inferInstanceAs (IsIso (((HomologicalComplex.eval _ _ (-1)).mapIso
      (oneKoszulSquareConeIso a)).hom))
  apply (cancel_mono ((oneKoszulSquareConeIso a).hom.f (-1))).mp
  rw [Category.assoc, ← (oneKoszulSquareConeIso a).hom.comm (-2) (-1),
    ← Category.assoc, oneKoszulSquareTop_cone, oneKoszulSquareConeTop_d,
    Preadditive.sub_comp, Linear.smul_comp, Linear.smul_comp,
    oneKoszulSquareRight_cone, oneKoszulSquareLeft_cone]

abbrev oneKoszulSquareConeDegreeIso (a : R) (n : ℤ) :=
  (HomologicalComplex.eval _ _ n).mapIso (oneKoszulSquareConeIso a)

@[reassoc]
lemma oneKoszulSquareConeBottom_unmap (a : R) :
    oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv =
      oneKoszulSquareBottom a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a 0)).mpr
    (oneKoszulSquareBottom_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeLeft_unmap (a : R) :
    oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv =
      oneKoszulSquareLeft a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-1))).mpr
    (oneKoszulSquareLeft_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeRight_unmap (a : R) :
    oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv =
      oneKoszulSquareRight a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-1))).mpr
    (oneKoszulSquareRight_cone a)).symm

@[reassoc]
lemma oneKoszulSquareConeTop_unmap (a : R) :
    oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv =
      oneKoszulSquareTop a :=
  ((Iso.eq_comp_inv (oneKoszulSquareConeDegreeIso a (-2))).mpr
    (oneKoszulSquareTop_cone a)).symm

lemma oneKoszulSquareXZero_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X 0 ⟶ Y}
    (h : oneKoszulSquareBottom a ≫ f = oneKoszulSquareBottom a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a 0).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) 1 0 rfl
  · exact (oneKoszul_isZero_X_other a 1 (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    change oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv ≫ f =
      oneKoszulSquareConeBottom a ≫ (oneKoszulSquareConeDegreeIso a 0).inv ≫ g
    exact (oneKoszulSquareConeBottom_unmap_assoc a f).trans
      (h.trans (oneKoszulSquareConeBottom_unmap_assoc a g).symm)

lemma oneKoszulSquareXNegOne_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X (-1) ⟶ Y}
    (hl : oneKoszulSquareLeft a ≫ f = oneKoszulSquareLeft a ≫ g)
    (hr : oneKoszulSquareRight a ≫ f = oneKoszulSquareRight a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a (-1)).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) 0 (-1) (by omega)
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    change oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ f =
      oneKoszulSquareConeLeft a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ g
    exact (oneKoszulSquareConeLeft_unmap_assoc a f).trans
      (hl.trans (oneKoszulSquareConeLeft_unmap_assoc a g).symm)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    change oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ f =
      oneKoszulSquareConeRight a ≫ (oneKoszulSquareConeDegreeIso a (-1)).inv ≫ g
    exact (oneKoszulSquareConeRight_unmap_assoc a f).trans
      (hr.trans (oneKoszulSquareConeRight_unmap_assoc a g).symm)

lemma oneKoszulSquareXNegTwo_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorSquare (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h : oneKoszulSquareTop a ≫ f = oneKoszulSquareTop a ≫ g) : f = g := by
  apply (cancel_epi (oneKoszulSquareConeDegreeIso a (-2)).inv).mp
  apply mappingCone.ext_from (smulId a (oneKoszulComplex a)) (-1) (-2) (by omega)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    change oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv ≫ f =
      oneKoszulSquareConeTop a ≫ (oneKoszulSquareConeDegreeIso a (-2)).inv ≫ g
    exact (oneKoszulSquareConeTop_unmap_assoc a f).trans
      (h.trans (oneKoszulSquareConeTop_unmap_assoc a g).symm)
  · exact (oneKoszul_isZero_X_other a (-2) (by omega)).eq_of_src _ _

end Adams
end SerrePositivity
