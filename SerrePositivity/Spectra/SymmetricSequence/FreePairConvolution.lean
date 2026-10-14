module

public import SerrePositivity.Spectra.SymmetricSequence.FreeConvolution
public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons

/-! # 二つの自由対称列のconvolutionと和次数の自由生成 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open LawfulDayConvolutionMonoidalCategoryStruct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]

/-- 二つの自由対称列の各項の積からの射は、全ての余積成分で決まる。 -/
lemma freePairComponent_hom_ext (m n : ℕ) (X Y : C) (a b : FiniteBijection) {Z : C}
    (f g : ((freeAt m).obj X).obj a ⊗ ((freeAt n).obj Y).obj b ⟶ Z)
    (h : ∀ (i : FiniteBijection.of m ⟶ a) (j : FiniteBijection.of n ⟶ b),
      (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫ f =
        (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorRight (((freeAt n).obj Y).obj b))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of m ⟶ a => X)))).hom_ext
  intro i
  apply (isColimitOfPreserves (tensorLeft X)
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ b => Y)))).hom_ext
  intro j
  change X ◁ freeAtInclusion n Y j.as ≫ (freeAtInclusion m X i.as ▷ _ ≫ f) =
    X ◁ freeAtInclusion n Y j.as ≫ (freeAtInclusion m X i.as ▷ _ ≫ g)
  simpa only [tensorHom_def', Category.assoc] using h i.as j.as

/-- 自由対称列の二つの余積成分に指定した射を、項の積へ延長する。 -/
def freePairComponentDesc (m n : ℕ) (X Y : C) (a b : FiniteBijection) {Z : C}
    (f : (FiniteBijection.of m ⟶ a) → (FiniteBijection.of n ⟶ b) → (X ⊗ Y ⟶ Z)) :
    ((freeAt m).obj X).obj a ⊗ ((freeAt n).obj Y).obj b ⟶ Z :=
  (isColimitOfPreserves (tensorRight (((freeAt n).obj Y).obj b))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of m ⟶ a => X)))).desc
      { pt := Z
        ι.app i := (isColimitOfPreserves (tensorLeft X)
          (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ b => Y)))).desc
            { pt := Z
              ι.app j := f i.as j.as
              ι.naturality i j k := by
                have : i = j := Discrete.ext (Discrete.eq_of_hom k)
                subst j
                simp }
        ι.naturality i j k := by
          have : i = j := Discrete.ext (Discrete.eq_of_hom k)
          subst j
          simp }

/-- 二つの余積成分からの延長は指定された射に一致する。 -/
@[reassoc] lemma freePairComponentDesc_fac (m n : ℕ) (X Y : C) (a b : FiniteBijection)
    {Z : C} (f : (FiniteBijection.of m ⟶ a) → (FiniteBijection.of n ⟶ b) → (X ⊗ Y ⟶ Z))
    (i : FiniteBijection.of m ⟶ a) (j : FiniteBijection.of n ⟶ b) :
    (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
        freePairComponentDesc m n X Y a b f = f i j := by
  simp only [tensorHom_def', Category.assoc, freePairComponentDesc]
  erw [(isColimitOfPreserves (tensorRight (((freeAt n).obj Y).obj b))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of m ⟶ a => X)))).fac _ ⟨i⟩]
  exact (isColimitOfPreserves (tensorLeft X)
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ b => Y)))).fac _ ⟨j⟩

/-- 和次数の射から、自由対称列の外部積の自然変換を構成する。 -/
def freePairExternalLift (m n : ℕ) (X Y : C) (H : SymmetricSequence C)
    (f : X ⊗ Y ⟶ level H (m + n)) :
    externalProduct ((freeAt m).obj X) ((freeAt n).obj Y) ⟶ FiniteBijection.sumFunctor ⋙ H where
  app ab := freePairComponentDesc m n X Y ab.1 ab.2
    (fun i j => f ≫ H.map (FiniteBijection.sumMap i j))
  naturality ab cd k := by
    apply freePairComponent_hom_ext m n X Y ab.1 ab.2
    intro i j
    change (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
        ((((freeAt m).obj X).map k.1 ▷ ((freeAt n).obj Y).obj ab.2) ≫
          ((freeAt m).obj X).obj cd.1 ◁ ((freeAt n).obj Y).map k.2) ≫
          freePairComponentDesc m n X Y cd.1 cd.2
            (fun i j => f ≫ H.map (FiniteBijection.sumMap i j)) =
      (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
        freePairComponentDesc m n X Y ab.1 ab.2
          (fun i j => f ≫ H.map (FiniteBijection.sumMap i j)) ≫
            H.map (FiniteBijection.sumMap k.1 k.2)
    rw [← tensorHom_def, ← Category.assoc, tensorHom_comp_tensorHom,
      freeAtInclusion_map, freeAtInclusion_map, freePairComponentDesc_fac]
    rw [freePairComponentDesc_fac_assoc, Category.assoc, ← H.map_comp,
      FiniteBijection.sumMap_comp]

/-- 和次数の射を二つの自由対称列のconvolutionからの射へ延長する。 -/
def freePairConvolutionLift (m n : ℕ) (X Y : C) (H : SymmetricSequence C)
    (f : X ⊗ Y ⟶ level H (m + n)) :
    convolution ((freeAt m).obj X) ((freeAt n).obj Y) ⟶ H :=
  (convolutionHomEquiv _ _ H).symm (freePairExternalLift m n X Y H f)

/-- 二つの自由対称列の積の和次数の生成元。 -/
def freePairConvolutionGenerator (m n : ℕ) (X Y : C) :
    X ⊗ Y ⟶ level (convolution ((freeAt m).obj X) ((freeAt n).obj Y)) (m + n) :=
  (freeAtGenerator m X ⊗ₘ freeAtGenerator n Y) ≫
    (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app
      (FiniteBijection.of m, FiniteBijection.of n)

/-- 延長射は外部積の余積成分上で指定された移送に一致する。 -/
@[reassoc] lemma freePairConvolutionLift_fac (m n : ℕ) (X Y : C) (H : SymmetricSequence C)
    (f : X ⊗ Y ⟶ level H (m + n)) (a b : FiniteBijection)
    (i : FiniteBijection.of m ⟶ a) (j : FiniteBijection.of n ⟶ b) :
    (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
        (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app (a, b) ≫
          (freePairConvolutionLift m n X Y H f).app (FiniteBijection.sumObj a b) =
      f ≫ H.map (FiniteBijection.sumMap i j) := by
  have h := (convolutionHomEquiv ((freeAt m).obj X) ((freeAt n).obj Y) H).apply_symm_apply
    (freePairExternalLift m n X Y H f)
  have ha := congrArg (fun k => k.app (a, b)) h
  change (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app (a, b) ≫
    (freePairConvolutionLift m n X Y H f).app (FiniteBijection.sumObj a b) =
      freePairComponentDesc m n X Y a b (fun i j => f ≫ H.map (FiniteBijection.sumMap i j)) at ha
  rw [ha, freePairComponentDesc_fac]

/-- 延長は和次数の生成元上で指定された射に一致する。 -/
@[reassoc] lemma freePairConvolutionGenerator_lift (m n : ℕ) (X Y : C)
    (H : SymmetricSequence C) (f : X ⊗ Y ⟶ level H (m + n)) :
    freePairConvolutionGenerator m n X Y ≫
      (freePairConvolutionLift m n X Y H f).app (FiniteBijection.of (m + n)) = f := by
  dsimp only [level] at *
  have h := freePairConvolutionLift_fac m n X Y H f _ _ (𝟙 _) (𝟙 _)
  simp only [FiniteBijection.sumMap_id, FiniteBijection.sumObj,
    FiniteBijection.card_of, CategoryTheory.Functor.map_id] at h
  simpa only [freePairConvolutionGenerator, freeAtGenerator, freeAtInclusion,
    Category.assoc, FiniteBijection.sumMap_id, CategoryTheory.Functor.map_id,
    Category.comp_id, FiniteBijection.sumObj, FiniteBijection.card_of] using
      h.trans (Category.comp_id f)

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- 各余積成分の積は、和次数の生成元を直和の全単射で移送して得られる。 -/
@[reassoc] lemma freePairConvolutionGenerator_transport (m n : ℕ) (X Y : C)
    (a b : FiniteBijection) (i : FiniteBijection.of m ⟶ a) (j : FiniteBijection.of n ⟶ b) :
    (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
        (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app (a, b) =
      freePairConvolutionGenerator m n X Y ≫
        (convolution ((freeAt m).obj X) ((freeAt n).obj Y)).map (FiniteBijection.sumMap i j) := by
  have h := (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).naturality
    (show (FiniteBijection.of m, FiniteBijection.of n) ⟶ (a, b) from (i, j))
  change ((((freeAt m).obj X).map i ▷ _) ≫
      (((freeAt m).obj X).obj a ◁ ((freeAt n).obj Y).map j)) ≫
        (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app (a, b) =
    (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app
      (FiniteBijection.of m, FiniteBijection.of n) ≫
        (convolution ((freeAt m).obj X) ((freeAt n).obj Y)).map
          (FiniteBijection.sumMap i j) at h
  rw [← tensorHom_def] at h
  rw [← freeAtInclusion_eq_generator, ← freeAtInclusion_eq_generator,
    ← tensorHom_comp_tensorHom, Category.assoc, h]
  simp only [freePairConvolutionGenerator, Category.assoc]

/-- 二つの自由対称列のconvolutionからの射は和次数の生成元で決まる。 -/
lemma freePairConvolution_hom_ext (m n : ℕ) (X Y : C) {H : SymmetricSequence C}
    (f g : convolution ((freeAt m).obj X) ((freeAt n).obj Y) ⟶ H)
    (h : freePairConvolutionGenerator m n X Y ≫ f.app (FiniteBijection.of (m + n)) =
      freePairConvolutionGenerator m n X Y ≫ g.app (FiniteBijection.of (m + n))) : f = g := by
  apply (convolutionHomEquiv _ _ H).injective
  apply NatTrans.ext
  funext ab
  apply freePairComponent_hom_ext m n X Y ab.1 ab.2
  intro i j
  change (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
      (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app ab ≫ f.app _ =
    (freeAtInclusion m X i ⊗ₘ freeAtInclusion n Y j) ≫
      (convolutionUnit ((freeAt m).obj X) ((freeAt n).obj Y)).app ab ≫ g.app _
  rw [freePairConvolutionGenerator_transport_assoc,
    freePairConvolutionGenerator_transport_assoc]
  erw [f.naturality, g.naturality]
  rw [← Category.assoc, ← Category.assoc, h]

/-- 二つの自由対称列のconvolutionは和次数から生成する自由対称列と同型。 -/
def freePairConvolutionIso (m n : ℕ) (X Y : C) :
    convolution ((freeAt m).obj X) ((freeAt n).obj Y) ≅ (freeAt (m + n)).obj (X ⊗ Y) where
  hom := freePairConvolutionLift m n X Y _ (freeAtGenerator (m + n) (X ⊗ Y))
  inv := freeAtLift (m + n) _ (freePairConvolutionGenerator m n X Y)
  hom_inv_id := by
    apply freePairConvolution_hom_ext m n X Y
    change freePairConvolutionGenerator m n X Y ≫
        (freePairConvolutionLift m n X Y _ (freeAtGenerator (m + n) (X ⊗ Y))).app _ ≫
          (freeAtLift (m + n) _ (freePairConvolutionGenerator m n X Y)).app _ =
      freePairConvolutionGenerator m n X Y ≫ 𝟙 _
    rw [freePairConvolutionGenerator_lift_assoc, freeAtGenerator_lift, Category.comp_id]
  inv_hom_id := by
    apply ((freeAtAdjunction (C := C) (m + n)).homEquiv (X ⊗ Y) _).injective
    rw [freeAtHomEquiv_apply, freeAtHomEquiv_apply]
    change freeAtGenerator (m + n) (X ⊗ Y) ≫
        (freeAtLift (m + n) _ (freePairConvolutionGenerator m n X Y)).app _ ≫
          (freePairConvolutionLift m n X Y _ (freeAtGenerator (m + n) (X ⊗ Y))).app _ =
      freeAtGenerator (m + n) (X ⊗ Y) ≫ 𝟙 _
    rw [← Category.assoc, freeAtGenerator_lift, freePairConvolutionGenerator_lift,
      Category.comp_id]

/-- 和次数の比較の順方向は二つの生成元の積を和次数の生成元へ送る。 -/
@[reassoc] lemma freePairConvolutionIso_generator_hom (m n : ℕ) (X Y : C) :
    freePairConvolutionGenerator m n X Y ≫
        (freePairConvolutionIso m n X Y).hom.app (FiniteBijection.of (m + n)) =
      freeAtGenerator (m + n) (X ⊗ Y) := freePairConvolutionGenerator_lift m n X Y _ _

/-- 和次数の比較の逆方向は和次数の生成元を二つの生成元の積へ送る。 -/
@[reassoc] lemma freePairConvolutionIso_generator_inv (m n : ℕ) (X Y : C) :
    freeAtGenerator (m + n) (X ⊗ Y) ≫
        (freePairConvolutionIso m n X Y).inv.app (FiniteBijection.of (m + n)) =
      freePairConvolutionGenerator m n X Y := freeAtGenerator_lift (m + n) _ _

/-- 二つの自由対称列の積の生成元は両方の入力の射と両立する。 -/
@[reassoc] lemma freePairConvolutionGenerator_input (m n : ℕ) {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    freePairConvolutionGenerator m n X Y ≫
        (((freeAt m).map f) ⊗ₘ ((freeAt n).map g)).app (FiniteBijection.of (m + n)) =
      (f ⊗ₘ g) ≫ freePairConvolutionGenerator m n X' Y' := by
  have hn := convolutionExtensionUnit_comp_ι_map_tensorHom_app FiniteBijection C
      ((freeAt m).map f) ((freeAt n).map g) (FiniteBijection.of m) (FiniteBijection.of n)
  simp only [lawfulConvolutionExtensionUnit_app, lawfulEmbedding_eq, toFunctorCategory,
    indexTensor_eq_sum, FiniteBijection.sumObj, FiniteBijection.card_of] at hn
  have hf : freeAtGenerator m X ≫ ((freeAt m).map f).app (FiniteBijection.of m) =
      f ≫ freeAtGenerator m X' := freeAtInclusion_map_input m f (𝟙 _)
  have hg : freeAtGenerator n Y ≫ ((freeAt n).map g).app (FiniteBijection.of n) =
      g ≫ freeAtGenerator n Y' := freeAtInclusion_map_input n g (𝟙 _)
  simp only [freePairConvolutionGenerator, Category.assoc]
  rw [hn, ← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc]

/-- 和次数への自由生成の比較は両方の入力に関して自然。 -/
lemma freePairConvolutionIso_naturality (m n : ℕ) {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (((freeAt m).map f) ⊗ₘ ((freeAt n).map g)) ≫ (freePairConvolutionIso m n X' Y').hom =
      (freePairConvolutionIso m n X Y).hom ≫ (freeAt (m + n)).map (f ⊗ₘ g) := by
  apply freePairConvolution_hom_ext m n X Y
  change freePairConvolutionGenerator m n X Y ≫
      (((freeAt m).map f) ⊗ₘ ((freeAt n).map g)).app _ ≫
        (freePairConvolutionIso m n X' Y').hom.app _ =
    freePairConvolutionGenerator m n X Y ≫ (freePairConvolutionIso m n X Y).hom.app _ ≫
      ((freeAt (m + n)).map (f ⊗ₘ g)).app _
  rw [freePairConvolutionGenerator_input_assoc, freePairConvolutionIso_generator_hom,
    freePairConvolutionIso_generator_hom_assoc]
  exact (freeAtInclusion_map_input (m + n) (f ⊗ₘ g) (𝟙 _)).symm

end SerrePositivity.SymmetricSequence
