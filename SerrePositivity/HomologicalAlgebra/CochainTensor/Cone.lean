module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.Flat.CategoryTheory
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # テンソル積と写像錐・シフト・単一複体・非輪状性

## 概要

テンソル積と写像錐の比較、シフトとの比較（左は符号なし、右は (-1)^(i*s)）と加法性、零次に置いた複体とのテンソルを項ごとのテンソル関手と同一視すること、非輪状な複体と有界な平坦複体のテンソルが非輪状であることを与える。

## 方針

全複体の項ごとの同型を作り、微分の符号を確かめる。

## 規約

右のシフトの比較には符号が付く。

## 使われ方

PerfectComplex のテンソル、導来テンソル、Koszul 複体。
-/

@[expose] public noncomputable section

universe u

section CochainTensorShiftPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Shift the left factor of the tensor complex. -/
abbrev cochainTensorShiftLeft (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℤ) :
    cochainTensor (P⟦s⟧) Q ≅ (cochainTensor P Q)⟦s⟧ :=
  CochainComplex.mapBifunctorShift₁Iso P Q (curriedTensor (ModuleCat.{u} R)) s

/-- Shift the right factor, including its totalization sign. -/
abbrev cochainTensorShiftRight (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℤ) :
    cochainTensor P (Q⟦s⟧) ≅ (cochainTensor P Q)⟦s⟧ :=
  CochainComplex.mapBifunctorShift₂Iso P Q (curriedTensor (ModuleCat.{u} R)) s

@[reassoc]
lemma cochainTensorShiftLeft_naturality {P P' Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (s : ℤ) :
    cochainTensorMap (f⟦s⟧') (𝟙 Q) ≫ (cochainTensorShiftLeft P' Q s).hom =
      (cochainTensorShiftLeft P Q s).hom ≫ (cochainTensorMap f (𝟙 Q))⟦s⟧' :=
  CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁ f Q
    (curriedTensor (ModuleCat.{u} R)) s

@[reassoc]
lemma cochainTensorShiftRight_naturality {P Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : Q ⟶ Q') (s : ℤ) :
    cochainTensorMap (𝟙 P) (g⟦s⟧') ≫ (cochainTensorShiftRight P Q' s).hom =
      (cochainTensorShiftRight P Q s).hom ≫ (cochainTensorMap (𝟙 P) g)⟦s⟧' :=
  CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂ P g
    (curriedTensor (ModuleCat.{u} R)) s

/-- Homogeneous formula for the sign-free left shift comparison. -/
@[reassoc]
lemma ιTensorObj_cochainTensorShiftLeft (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (s i j n : ℤ) (h : i + j = n) :
    ιTensorObj (P⟦s⟧) Q i j n h ≫ (cochainTensorShiftLeft P Q s).hom.f n =
      ((CochainComplex.shiftFunctorObjXIso P s i (i + s) rfl).hom ▷ Q.X j) ≫
        ιTensorObj P Q (i + s) j (n + s) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso (cochainTensor P Q) s n (n + s) rfl).inv :=
  CochainComplex.ι_mapBifunctorShift₁Iso_hom_f P Q (curriedTensor (ModuleCat.{u} R))
    s i j n h (i + s) (n + s) rfl rfl

/-- Homogeneous formula for the sign in the right shift comparison. -/
@[reassoc]
lemma ιTensorObj_cochainTensorShiftRight (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (s i j n : ℤ) (h : i + j = n) :
    ιTensorObj P (Q⟦s⟧) i j n h ≫ (cochainTensorShiftRight P Q s).hom.f n =
      (i * s).negOnePow •
        (P.X i ◁ (CochainComplex.shiftFunctorObjXIso Q s j (j + s) rfl).hom) ≫
          ιTensorObj P Q i (j + s) (n + s) (by omega) ≫
            (CochainComplex.shiftFunctorObjXIso (cochainTensor P Q) s n (n + s) rfl).inv :=
  CochainComplex.ι_mapBifunctorShift₂Iso_hom_f P Q (curriedTensor (ModuleCat.{u} R))
    s i j n h (j + s) (n + s) rfl rfl

/-- The functor of tensoring on the right with a fixed complex. -/
abbrev cochainTensorFixedRight (Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj Q

/-- The functor of tensoring on the left with a fixed complex. -/
abbrev cochainTensorFixedLeft (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P

instance (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedRight Q).Additive where
  map_add := cochainTensorMap_add_left _ _ (𝟙 Q)

instance (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedLeft P).Additive where
  map_add := cochainTensorMap_add_right (𝟙 P) _ _

end SerrePositivity

end CochainTensorShiftPart

section CochainTensorConePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end SerrePositivity

end CochainTensorConePart

section CochainTensorSinglePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The complex concentrated in degree zero with value V. -/
abbrev cochainSingleZero (V : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj V

variable (V : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Collapse the homogeneous coproduct when the left factor is concentrated in degree zero. -/
def tensorSingleLeftDesc (n : ℤ) :
    (cochainTensor (cochainSingleZero V) P).X n ⟶ V ⊗ P.X n :=
  HomologicalComplex₂.totalDesc _ (fun i j h => by
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at h; omega
      subst j
      exact (singleObjXSelf (.up ℤ) 0 V).hom ▷ P.X n
    · exact 0)

@[reassoc (attr := simp)]
lemma ι_tensorSingleLeftDesc (n : ℤ) :
    ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫ tensorSingleLeftDesc V P n =
      (singleObjXSelf (.up ℤ) 0 V).hom ▷ P.X n := by
  simp [tensorSingleLeftDesc]

/-- Degreewise comparison with the ordinary pointwise tensor. -/
def tensorSingleLeftXIso (n : ℤ) :
    (cochainTensor (cochainSingleZero V) P).X n ≅ V ⊗ P.X n where
  hom := tensorSingleLeftDesc V P n
  inv := (singleObjXSelf (.up ℤ) 0 V).inv ▷ P.X n ≫
    ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at h; omega
      subst j
      simp [← comp_whiskerRight_assoc, -comp_whiskerRight]
    · have hz : IsZero ((cochainSingleZero V).X i) := isZero_single_obj_X _ _ _ i hi
      exact ((tensorRight (P.X j)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    simp [-comp_whiskerRight]

/-- The inverse comparison intertwines the pointwise and total tensor differentials. -/
@[reassoc]
lemma tensorSingleLeftXIso_inv_d (n m : ℤ) (h : (ComplexShape.up ℤ).Rel n m) :
    (tensorSingleLeftXIso V P n).inv ≫ (cochainTensor (cochainSingleZero V) P).d n m =
      (V ◁ P.d n m) ≫ (tensorSingleLeftXIso V P m).inv := by
  dsimp at h
  subst m
  dsimp only [tensorSingleLeftXIso]
  rw [Category.assoc, ιTensorObj_cochainTensor_d]
  simp only [single_obj_d, MonoidalPreadditive.zero_whiskerRight, zero_comp, zero_add,
    Int.negOnePow_zero, one_smul, ← whisker_exchange_assoc]

/-- The total tensor with a degree-zero complex is naturally the ordinary tensor functor. -/
def cochainTensorSingleLeftIso :
    cochainTensor (cochainSingleZero V) P ≅ ((tensorLeft V).mapHomologicalComplex (.up ℤ)).obj P :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => (tensorSingleLeftXIso V P n).symm)
    (fun n m h => tensorSingleLeftXIso_inv_d V P n m h)).symm

/-- Tensoring an acyclic complex with a flat module preserves acyclicity. -/
lemma cochainTensorSingleLeft_acyclic [Module.Flat R V] (hP : P.Acyclic) :
    (cochainTensor (cochainSingleZero V) P).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : IsZero ((((tensorLeft V).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
    exact ((P.sc i).mapHomologyIso (tensorLeft V)).isZero_iff.mpr
      ((tensorLeft V).map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology P i).mp (hP i)))
  exact ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (cochainTensorSingleLeftIso V P)).isZero_iff.mpr hz
end SerrePositivity

end CochainTensorSinglePart

section CochainTensorAcyclicPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A degreewise split sequence propagates tensor acyclicity from outer to middle terms. -/
lemma cochainTensor_acyclic_of_degreewiseSplit
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (h₁ : (cochainTensor S.X₁ P).Acyclic) (h₃ : (cochainTensor S.X₃ P).Acyclic) :
    (cochainTensor S.X₂ P).Acyclic := by
  let f := CochainComplex.homOfDegreewiseSplit S σ
  have hshift : (cochainTensor (S.X₁⟦(1 : ℤ)⟧) P).Acyclic :=
    cochainAcyclic_of_iso (cochainAcyclic_shift h₁ 1) (cochainTensorShiftLeft S.X₁ P 1).symm
  have hc := cochainAcyclic_mappingCone (cochainTensorMap f (𝟙 P)) h₃ hshift
  have ht : (cochainTensor (CochainComplex.mappingCone f) P).Acyclic :=
    cochainAcyclic_of_iso hc (cochainTensorConeLeft f P).symm
  let e := CochainComplex.mappingConeHomOfDegreewiseSplitIso S σ
  have he : (cochainTensor (S.X₂⟦(1 : ℤ)⟧) P).Acyclic :=
    cochainAcyclic_of_homotopyEquiv ht
      (cochainTensorHomotopyEquiv (HomotopyEquiv.ofIso e) (HomotopyEquiv.refl P))
  exact cochainAcyclic_of_shift 1 (cochainAcyclic_of_iso he (cochainTensorShiftLeft S.X₂ P 1))

/-- A complex concentrated in degree zero is isomorphic to its single nonzero term. -/
def cochainIsoSingleZero (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hQ : ∀ i : ℤ, i ≠ 0 → IsZero (Q.X i)) : Q ≅ cochainSingleZero (Q.X 0) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => by
    by_cases hi : i = 0
    · subst i
      exact (singleObjXSelf (.up ℤ) 0 (Q.X 0)).symm
    · exact (hQ i hi).iso (isZero_single_obj_X _ _ _ i hi)) (by
      intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by dsimp at hij; omega
        exact (isZero_single_obj_X (.up ℤ) 0 (Q.X 0) j hj).eq_of_tgt _ _
      · exact (hQ i hi).eq_of_src _ _)

lemma cochainTensor_concentratedZero_acyclic
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hQ : ∀ i : ℤ, i ≠ 0 → IsZero (Q.X i)) [Module.Flat R (Q.X 0)] (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have h := cochainTensorSingleLeft_acyclic (Q.X 0) P hP
  exact cochainAcyclic_of_homotopyEquiv h
    (cochainTensorHomotopyEquiv (HomotopyEquiv.ofIso (cochainIsoSingleZero Q hQ).symm)
      (HomotopyEquiv.refl P))

/-- A complex with one flat term in any degree preserves acyclicity under tensor. -/
lemma cochainTensor_concentrated_acyclic
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hQ : ∀ i : ℤ, i ≠ a → IsZero (Q.X i)) [Module.Flat R (Q.X a)] (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero ((Q⟦a⟧).X i) :=
    (Q.shiftFunctorObjXIso a i (i + a) rfl).isZero_iff.mpr (hQ (i + a) (by omega))
  have : Module.Flat R ((Q⟦a⟧).X 0) :=
    Module.Flat.of_linearEquiv (Q.shiftFunctorObjXIso a 0 a (by omega)).toLinearEquiv
  have h := cochainTensor_concentratedZero_acyclic (Q⟦a⟧) P hz hP
  exact cochainAcyclic_of_shift a (cochainAcyclic_of_iso h (cochainTensorShiftLeft Q P a))

/-- A bounded complex of flat modules preserves acyclicity of any other complex. -/
lemma cochainTensor_acyclic_of_flat_bounds
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hQa : ∀ i, i < a → IsZero (Q.X i))
    (hQb : ∀ i, b < i → IsZero (Q.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (hP : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  have H : ∀ n : ℕ, ∀ (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ),
      (∀ i, i < a → IsZero (Q.X i)) →
      (∀ i, a + n < i → IsZero (Q.X i)) →
      (∀ i, Module.Flat R (Q.X i)) → (cochainTensor Q P).Acyclic := by
    intro n
    induction n with
    | zero =>
      intro Q a ha hb hf
      have hz (i : ℤ) (hi : i ≠ a) : IsZero (Q.X i) := by
        by_cases hia : i < a
        · exact ha i hia
        · exact hb i (by simp; omega)
      have := hf a
      exact cochainTensor_concentrated_acyclic Q P a hz hP
    | succ n ih =>
      intro Q a ha hb hf
      let S := StupidTruncation.shortComplex Q (a + 1)
      have h₁a (i : ℤ) (hi : i < a + 1) : IsZero (S.X₁.X i) :=
        StupidTruncation.above_isZero_X Q (a + 1) i hi
      have h₁b (i : ℤ) (hi : a + 1 + n < i) : IsZero (S.X₁.X i) := by
        have hge : a + 1 ≤ i := by omega
        exact (StupidTruncation.aboveXIso Q (a + 1) i hge).isZero_iff.mpr
          (hb i (by push_cast; omega))
      have h₁flat (i : ℤ) : Module.Flat R (S.X₁.X i) := by
        by_cases hge : a + 1 ≤ i
        · have := hf i
          exact Module.Flat.of_linearEquiv
            (StupidTruncation.aboveXIso Q (a + 1) i hge).toLinearEquiv
        · have := ModuleCat.subsingleton_of_isZero (h₁a i (by omega))
          infer_instance
      have h₁ := ih S.X₁ (a + 1) h₁a h₁b h₁flat
      have h₃zero (i : ℤ) (hi : i ≠ a) : IsZero (S.X₃.X i) := by
        by_cases hia : i < a
        · exact (StupidTruncation.belowXIso Q (a + 1 - 1) i (by omega)).isZero_iff.mpr (ha i hia)
        · exact StupidTruncation.below_isZero_X Q (a + 1 - 1) i (by omega)
      have : Module.Flat R (S.X₃.X a) := by
        have := hf a
        exact Module.Flat.of_linearEquiv (StupidTruncation.belowXIso Q (a + 1 - 1) a
          (by omega)).toLinearEquiv
      have h₃ := cochainTensor_concentrated_acyclic S.X₃ P a h₃zero hP
      exact cochainTensor_acyclic_of_degreewiseSplit S
        (StupidTruncation.splitting Q (a + 1)) P h₁ h₃
  exact H (b - a).toNat Q a hQa (fun i hi => hQb i (by omega)) hflat

/-- A bounded flat right factor preserves quasi-isomorphisms in an arbitrary left factor. -/
lemma cochainTensor_quasiIso_left_of_boundedFlat
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hQa : ∀ i, i < a → IsZero (Q.X i)) (hQb : ∀ i, b < i → IsZero (Q.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (f : P ⟶ P') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).mp inferInstance
  have ht := cochainTensor_acyclic_of_flat_bounds Q (CochainComplex.mappingCone f)
    a b hQa hQb hflat hc
  have ht' := cochainAcyclic_of_iso ht (cochainTensorSymmetry Q (CochainComplex.mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).mpr
    (cochainAcyclic_of_iso ht' (cochainTensorConeLeft f Q))

end SerrePositivity

end CochainTensorAcyclicPart
