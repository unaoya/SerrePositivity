module
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

/-! # Tensor products and mapping cones -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex Pretriangulated
open CochainComplex HomComplex
variable {R : Type u} [CommRing R]
variable {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P')
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)

lemma tensor_neg_whiskerRight {A B : ModuleCat.{u} R} (g : A ⟶ B) (T : ModuleCat.{u} R) :
    (-g) ▷ T = -(g ▷ T) := (tensorRight T).map_neg

/-- Cancellation of a shift component isomorphism inside a homogeneous tensor. -/
lemma tensor_shift_cancel {A B T U V : ModuleCat.{u} R} (e : A ≅ B)
    (a : U ⟶ B) (b : B ⊗ T ⟶ V) :
    (-(a ≫ e.inv)) ▷ T ≫ (A ◁ (𝟙 T)) ≫ (e.hom ▷ T) ≫ b = -(a ▷ T ≫ b) := by
  simp only [whiskerLeft_id, Category.id_comp, tensor_neg_whiskerRight, Preadditive.neg_comp]
  rw [neg_inj, comp_whiskerRight]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp]

/-- The projection of the tensor of a cone to its shifted left summand. -/
def tensorConeFstX (n : ℤ) :
    (cochainTensor (mappingCone f) Q).X n ⟶ (cochainTensor P Q).X (n + 1) :=
  HomologicalComplex₂.totalDesc _ (fun i j h =>
    ((mappingCone.fst f : Cochain (mappingCone f) P 1).v i (i + 1) rfl ▷ Q.X j) ≫
      ιTensorObj P Q (i + 1) j (n + 1) (by dsimp at h; omega))

/-- The projection of the tensor of a cone to its right summand. -/
def tensorConeSndX (n : ℤ) :
    (cochainTensor (mappingCone f) Q).X n ⟶ (cochainTensor P' Q).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j h =>
    ((mappingCone.snd f).v i i (add_zero i) ▷ Q.X j) ≫ ιTensorObj P' Q i j n h)

/-- The inclusion of the shifted left summand into the tensor of a cone. -/
def tensorConeInlX (n : ℤ) :
    (cochainTensor P Q).X (n + 1) ⟶ (cochainTensor (mappingCone f) Q).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j h =>
    ((mappingCone.inl f).v i (i - 1) (by omega) ▷ Q.X j) ≫
      ιTensorObj (mappingCone f) Q (i - 1) j n (by dsimp at h; omega))

@[reassoc (attr := simp)]
lemma ι_tensorConeFstX (i j n : ℤ) (h : i + j = n) :
    ιTensorObj (mappingCone f) Q i j n h ≫ tensorConeFstX f Q n =
      ((mappingCone.fst f : Cochain (mappingCone f) P 1).v i (i + 1) rfl ▷ Q.X j) ≫
        ιTensorObj P Q (i + 1) j (n + 1) (by omega) := by
  simp [tensorConeFstX]

@[reassoc (attr := simp)]
lemma ι_tensorConeSndX (i j n : ℤ) (h : i + j = n) :
    ιTensorObj (mappingCone f) Q i j n h ≫ tensorConeSndX f Q n =
      ((mappingCone.snd f).v i i (add_zero i) ▷ Q.X j) ≫ ιTensorObj P' Q i j n h := by
  simp [tensorConeSndX]

@[reassoc (attr := simp)]
lemma ι_tensorConeInlX (i j n : ℤ) (h : i + j = n + 1) :
    ιTensorObj P Q i j (n + 1) h ≫ tensorConeInlX f Q n =
      ((mappingCone.inl f).v i (i - 1) (by omega) ▷ Q.X j) ≫
        ιTensorObj (mappingCone f) Q (i - 1) j n (by omega) := by
  simp [tensorConeInlX]

/-- First projection with an explicitly chosen successor index. -/
@[reassoc]
lemma ι_tensorConeFstX' (i k j n : ℤ) (hk : k = i + 1) (h : i + j = n) :
    ιTensorObj (mappingCone f) Q i j n h ≫ tensorConeFstX f Q n =
      ((mappingCone.fst f : Cochain (mappingCone f) P 1).v i k (by omega) ▷ Q.X j) ≫
        ιTensorObj P Q k j (n + 1) (by omega) := by
  subst k
  exact ι_tensorConeFstX f Q i j n h

/-- Left inclusion with an explicitly chosen predecessor index. -/
@[reassoc]
lemma ι_tensorConeInlX' (i k j n : ℤ) (hk : k = i - 1) (h : i + j = n + 1) :
    ιTensorObj P Q i j (n + 1) h ≫ tensorConeInlX f Q n =
      ((mappingCone.inl f).v i k (by omega) ▷ Q.X j) ≫
        ιTensorObj (mappingCone f) Q k j n (by omega) := by
  subst k
  exact ι_tensorConeInlX f Q i j n h

@[reassoc (attr := simp)]
lemma tensorConeInlX_fst (n : ℤ) : tensorConeInlX f Q n ≫ tensorConeFstX f Q n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_tensorConeInlX_assoc, ι_tensorConeFstX' f Q (i - 1) i j n (by omega)]
  rw [← comp_whiskerRight_assoc, mappingCone.inl_v_fst_v]
  simp

@[reassoc (attr := simp)]
lemma tensorConeInlX_snd (n : ℤ) : tensorConeInlX f Q n ≫ tensorConeSndX f Q n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp [← comp_whiskerRight_assoc, -comp_whiskerRight, mappingCone.inl_v_snd_v]

@[reassoc (attr := simp)]
lemma tensorConeInrX_fst (n : ℤ) :
    (cochainTensorMap (mappingCone.inr f) (𝟙 Q)).f n ≫ tensorConeFstX f Q n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_mapBifunctorMap_assoc]
  simp [← comp_whiskerRight_assoc, -comp_whiskerRight, mappingCone.inr_f_fst_v]

@[reassoc (attr := simp)]
lemma tensorConeInrX_snd (n : ℤ) :
    (cochainTensorMap (mappingCone.inr f) (𝟙 Q)).f n ≫ tensorConeSndX f Q n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ι_mapBifunctorMap_assoc]
  simp [← comp_whiskerRight_assoc, -comp_whiskerRight, mappingCone.inr_f_snd_v]

lemma tensorCone_id_X (n : ℤ) :
    tensorConeFstX f Q n ≫ tensorConeInlX f Q n +
      tensorConeSndX f Q n ≫ (cochainTensorMap (mappingCone.inr f) (𝟙 Q)).f n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [Preadditive.comp_add, ι_tensorConeFstX_assoc, ι_tensorConeSndX_assoc,
    ι_tensorConeInlX' f Q (i + 1) i j n (by omega)]
  rw [ι_mapBifunctorMap, HomologicalComplex.id_f]
  change
    ((mappingCone.fst f : Cochain (mappingCone f) P 1).v i (i + 1) rfl ▷ Q.X j) ≫
        ((mappingCone.inl f).v (i + 1) i (by omega) ▷ Q.X j) ≫
          ιTensorObj (mappingCone f) Q i j n h +
      ((mappingCone.snd f).v i i (add_zero i) ▷ Q.X j) ≫
        ((mappingCone.inr f).f i ▷ Q.X j) ≫ (mappingCone f).X i ◁ (𝟙 (Q.X j)) ≫
          ιTensorObj (mappingCone f) Q i j n h = _
  simp only [whiskerLeft_id, Category.id_comp, ← comp_whiskerRight_assoc,
    ← Preadditive.add_comp, ← MonoidalPreadditive.add_whiskerRight,
    mappingCone.id_X, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- The first projection obeys the shifted differential. -/
lemma tensorCone_d_fst (n : ℤ) :
    (cochainTensor (mappingCone f) Q).d n (n + 1) ≫ tensorConeFstX f Q (n + 1) =
      -(tensorConeFstX f Q n ≫ (cochainTensor P Q).d (n + 1) (n + 1 + 1)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_cochainTensor_d_assoc]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, ι_tensorConeFstX,
    ι_tensorConeFstX_assoc, Preadditive.comp_neg, Category.assoc]
  rw [ιTensorObj_cochainTensor_d]
  simp only [Preadditive.comp_add, Linear.comp_units_smul, neg_add]
  simp only [← comp_whiskerRight_assoc, mappingCone.d_fst_v]
  rw [tensor_neg_whiskerRight, Preadditive.neg_comp, add_right_inj]
  rw [whisker_exchange_assoc]
  simp only [Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.neg_smul, neg_neg]

/-- The second projection obeys the cone differential, including its off-diagonal map. -/
lemma tensorCone_d_snd (n : ℤ) :
    (cochainTensor (mappingCone f) Q).d n (n + 1) ≫ tensorConeSndX f Q (n + 1) =
      tensorConeFstX f Q n ≫ (cochainTensorMap f (𝟙 Q)).f (n + 1) +
        tensorConeSndX f Q n ≫ (cochainTensor P' Q).d n (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_cochainTensor_d_assoc]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, ι_tensorConeSndX,
    Preadditive.comp_add, ι_tensorConeFstX_assoc, ι_tensorConeSndX_assoc, Category.assoc]
  rw [ι_mapBifunctorMap, ιTensorObj_cochainTensor_d]
  simp only [HomologicalComplex.id_f, Preadditive.comp_add, Linear.comp_units_smul]
  rw [← comp_whiskerRight_assoc, mappingCone.d_snd_v f i (i + 1) rfl]
  simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
    comp_whiskerRight_assoc, whisker_exchange_assoc]
  rw [← add_assoc, add_left_inj, add_left_inj]
  change _ = ((mappingCone.fst f : Cochain (mappingCone f) P 1).v i (i + 1) rfl ▷ Q.X j) ≫
    (f.f (i + 1) ▷ Q.X j) ≫ (P'.X (i + 1) ◁ (𝟙 (Q.X j))) ≫
      ιTensorObj P' Q (i + 1) j (n + 1) (by dsimp at h; omega)
  rw [whiskerLeft_id, Category.id_comp]

/-- The concrete degreewise comparison between a tensor cone and the cone of the tensor map. -/
def tensorConeXIso (n : ℤ) :
    (cochainTensor (mappingCone f) Q).X n ≅
      (mappingCone (cochainTensorMap f (𝟙 Q))).X n where
  hom := tensorConeFstX f Q n ≫
      (mappingCone.inl (cochainTensorMap f (𝟙 Q))).v (n + 1) n (by omega) +
    tensorConeSndX f Q n ≫ (mappingCone.inr (cochainTensorMap f (𝟙 Q))).f n
  inv := (mappingCone.fst (cochainTensorMap f (𝟙 Q)) :
      Cochain (mappingCone (cochainTensorMap f (𝟙 Q))) (cochainTensor P Q) 1).v n (n + 1) rfl ≫
      tensorConeInlX f Q n +
    (mappingCone.snd (cochainTensorMap f (𝟙 Q))).v n n (add_zero n) ≫
      (cochainTensorMap (mappingCone.inr f) (𝟙 Q)).f n
  hom_inv_id := by
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add]
    exact tensorCone_id_X f Q n
  inv_hom_id := by
    apply mappingCone.ext_from (cochainTensorMap f (𝟙 Q)) (n + 1) n rfl
    · simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    · simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
lemma tensorConeXIso_hom_fst (n : ℤ) :
    (tensorConeXIso f Q n).hom ≫
      (mappingCone.fst (cochainTensorMap f (𝟙 Q)) :
        Cochain (mappingCone (cochainTensorMap f (𝟙 Q))) (cochainTensor P Q) 1).v
        n (n + 1) rfl = tensorConeFstX f Q n := by
  simp [tensorConeXIso, Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
lemma tensorConeXIso_hom_snd (n : ℤ) :
    (tensorConeXIso f Q n).hom ≫
      (mappingCone.snd (cochainTensorMap f (𝟙 Q))).v n n (add_zero n) =
        tensorConeSndX f Q n := by
  simp [tensorConeXIso, Preadditive.add_comp, Category.assoc]

/-- Tensoring a mapping cone on the right is the mapping cone of the tensor map. -/
def cochainTensorConeLeft :
    cochainTensor (mappingCone f) Q ≅ mappingCone (cochainTensorMap f (𝟙 Q)) :=
  HomologicalComplex.Hom.isoOfComponents (tensorConeXIso f Q) (by
    intro n m h
    dsimp at h
    subst m
    apply mappingCone.ext_to (cochainTensorMap f (𝟙 Q)) (n + 1) (n + 1 + 1) rfl
    · simp only [Category.assoc, mappingCone.d_fst_v _ _ _ _ rfl rfl,
        Preadditive.comp_neg, tensorConeXIso_hom_fst, tensorConeXIso_hom_fst_assoc,
        tensorCone_d_fst]
    · simp only [Category.assoc, mappingCone.d_snd_v _ _ _ rfl,
        Preadditive.comp_add, tensorConeXIso_hom_fst_assoc, tensorConeXIso_hom_snd_assoc,
        tensorConeXIso_hom_snd, tensorCone_d_snd])

/-- The cone comparison preserves the inclusion of the right summand. -/
@[reassoc]
lemma cochainTensorConeLeft_inr :
    cochainTensorMap (mappingCone.inr f) (𝟙 Q) ≫ (cochainTensorConeLeft f Q).hom =
      mappingCone.inr (cochainTensorMap f (𝟙 Q)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mappingCone.ext_to (cochainTensorMap f (𝟙 Q)) n (n + 1) rfl
  · simp only [HomologicalComplex.comp_f, cochainTensorConeLeft,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Category.assoc,
      tensorConeXIso_hom_fst, tensorConeInrX_fst, mappingCone.inr_f_fst_v]
  · simp only [HomologicalComplex.comp_f, cochainTensorConeLeft,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Category.assoc,
      tensorConeXIso_hom_snd, tensorConeInrX_snd, mappingCone.inr_f_snd_v]

/-- The connecting map is preserved with the canonical left shift comparison. -/
@[reassoc]
lemma cochainTensorConeLeft_mor₃ :
    cochainTensorMap (mappingCone.triangle f).mor₃ (𝟙 Q) ≫
        (cochainTensorShiftLeft P Q (1 : ℤ)).hom =
      (cochainTensorConeLeft f Q).hom ≫
        (mappingCone.triangle (cochainTensorMap f (𝟙 Q))).mor₃ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [ι_mapBifunctorMap_assoc]
  change ((mappingCone.triangle f).mor₃.f i ▷ Q.X j) ≫
      ((P⟦(1 : ℤ)⟧).X i ◁ (𝟙 (Q.X j))) ≫
        ιTensorObj (P⟦(1 : ℤ)⟧) Q i j n h ≫ (cochainTensorShiftLeft P Q 1).hom.f n = _
  rw [ιTensorObj_cochainTensorShiftLeft]
  rw [coneTriangle_mor₃_f, coneTriangle_mor₃_f]
  change _ = ιTensorObj (mappingCone f) Q i j n h ≫
      (tensorConeXIso f Q n).hom ≫
        (-((mappingCone.fst (cochainTensorMap f (𝟙 Q)) :
          Cochain (mappingCone (cochainTensorMap f (𝟙 Q))) (cochainTensor P Q) 1).v
          n (n + 1) rfl ≫
            ((cochainTensor P Q).shiftFunctorObjXIso 1 n (n + 1) rfl).inv))
  simp only [Preadditive.comp_neg, tensorConeXIso_hom_fst_assoc,
    ι_tensorConeFstX_assoc]
  generalize (mappingCone.fst f : Cochain (mappingCone f) P 1).v i (i + 1) rfl = a
  change (-(a ≫ (P.shiftFunctorObjXIso 1 i (i + 1) rfl).inv)) ▷ Q.X j ≫
      ((P⟦(1 : ℤ)⟧).X i ◁ (𝟙 (Q.X j))) ≫
      ((P.shiftFunctorObjXIso 1 i (i + 1) rfl).hom ▷ Q.X j) ≫
      ιTensorObj P Q (i + 1) j (n + 1) (by dsimp at h; omega) ≫
      ((cochainTensor P Q).shiftFunctorObjXIso 1 n (n + 1) rfl).inv =
    -(a ▷ Q.X j ≫ ιTensorObj P Q (i + 1) j (n + 1) (by dsimp at h; omega) ≫
      ((cochainTensor P Q).shiftFunctorObjXIso 1 n (n + 1) rfl).inv)
  exact tensor_shift_cancel (P.shiftFunctorObjXIso 1 i (i + 1) rfl) a
    (ιTensorObj P Q (i + 1) j (n + 1) (by dsimp at h; omega) ≫
      ((cochainTensor P Q).shiftFunctorObjXIso 1 n (n + 1) rfl).inv)

/-- Tensoring on the right carries a concrete cone triangle to the tensor-map cone triangle. -/
def cochainTensorConeTriangleIso :
    (cochainTensorFixedRight Q).mapTriangle.obj (mappingCone.triangle f) ≅
      mappingCone.triangle (cochainTensorMap f (𝟙 Q)) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (cochainTensorConeLeft f Q) ?_ ?_ ?_
  · simp
  · simpa using cochainTensorConeLeft_inr f Q
  · simpa [Functor.commShiftIso_map₂CochainComplex_flip_hom_app] using
      cochainTensorConeLeft_mor₃ f Q
end SerrePositivity
