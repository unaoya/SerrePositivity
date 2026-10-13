module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotient
public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionNaturality

/-! # 明示的なブロック商の出力と入力の射

関係式を満たす生成元上の射を余等化子からの射へ降ろす。
添字への後合成と入力の第二因子への作用から、商の射と関手性を構成する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- ブロックの関係式を満たす生成元上の射の族を、商全体の射へ降ろす。 -/
def freeBlockQuotientDesc (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) {Y : C}
    (t : FreeBlockIndex n m → (F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶ Y))
    (ht : ∀ (σ : Equiv.Perm (Fin (m - n))) (h : FreeBlockIndex n m),
      F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫ t h =
        t (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h)) :
    freeBlockQuotient F n X m ⟶ Y :=
  coequalizer.desc (Sigma.desc t) (by
    apply Sigma.hom_ext
    intro r
    simp only [freeBlockRelationLeft, freeBlockRelationRight,
      Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
    exact ht r.1 r.2)

/-- 降下した射は各生成元上で指定された値に一致する。 -/
@[reassoc (attr := simp)] lemma freeBlockQuotientGenerator_desc
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) {Y : C}
    (t : FreeBlockIndex n m → (F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶ Y))
    (ht : ∀ (σ : Equiv.Perm (Fin (m - n))) (h : FreeBlockIndex n m),
      F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫ t h =
        t (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h))
    (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ freeBlockQuotientDesc F n X m t ht = t h := by
  simp only [freeBlockQuotientGenerator, freeBlockQuotientDesc, Category.assoc,
    coequalizer.π_desc, Sigma.ι_comp_desc]

/-- 出力の自己全単射を生成元の添字への後合成として商へ降ろす。 -/
def freeBlockQuotientOutputMap (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m) :
    freeBlockQuotient F n X m ⟶ freeBlockQuotient F n X m :=
  freeBlockQuotientDesc F n X m (fun h => freeBlockQuotientGenerator F n X m (h ≫ k))
    (fun σ h => by
      rw [freeBlockQuotientGenerator_relation]
      exact congrArg (freeBlockQuotientGenerator F n X m)
        (Category.assoc (FiniteBijection.sumMap
          (FiniteBijection.permutation (m - n) σ) (𝟙 _)) h k).symm)

/-- 商上の出力の射は生成元の添字へ後合成する。 -/
@[reassoc (attr := simp)] lemma freeBlockQuotientGenerator_output
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m) (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ freeBlockQuotientOutputMap F n X m k =
      freeBlockQuotientGenerator F n X m (h ≫ k) :=
  freeBlockQuotientGenerator_desc F n X m _ _ h

/-- 入力の射を各生成元の第二因子へ作用させ、商へ降ろす。 -/
def freeBlockQuotientInputMap (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) : freeBlockQuotient F n X m ⟶ freeBlockQuotient F n Y m :=
  freeBlockQuotientDesc F n X m
    (fun h => F.obj (FiniteBijection.of (m - n)) ◁ f ≫ freeBlockQuotientGenerator F n Y m h)
    (fun σ h => by
      rw [← whisker_exchange_assoc, freeBlockQuotientGenerator_relation])

/-- 商上の入力の射は生成元の第二因子へ作用する。 -/
@[reassoc (attr := simp)] lemma freeBlockQuotientGenerator_input
    (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ)
    (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ freeBlockQuotientInputMap F n f m =
      F.obj (FiniteBijection.of (m - n)) ◁ f ≫ freeBlockQuotientGenerator F n Y m h :=
  freeBlockQuotientGenerator_desc F n X m _ _ h

/-- 出力の恒等全単射は商上の恒等射。 -/
@[simp] lemma freeBlockQuotientOutputMap_id (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockQuotientOutputMap F n X m (𝟙 (FiniteBijection.of m)) = 𝟙 _ := by
  apply freeBlockQuotient_hom_ext
  intro h
  simp only [freeBlockQuotientGenerator_output, Category.comp_id]

/-- 出力の全単射の合成は商上の射の合成。 -/
lemma freeBlockQuotientOutputMap_comp (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (k l : FiniteBijection.of m ⟶ FiniteBijection.of m) :
    freeBlockQuotientOutputMap F n X m (k ≫ l) =
      freeBlockQuotientOutputMap F n X m k ≫ freeBlockQuotientOutputMap F n X m l := by
  apply freeBlockQuotient_hom_ext
  intro h
  simp only [freeBlockQuotientGenerator_output, freeBlockQuotientGenerator_output_assoc,
    Category.assoc]

/-- 入力の恒等射は商上の恒等射。 -/
@[simp] lemma freeBlockQuotientInputMap_id (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockQuotientInputMap F n (𝟙 X) m = 𝟙 _ := by
  apply freeBlockQuotient_hom_ext
  intro h
  simp only [freeBlockQuotientGenerator_input, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- 入力の射の合成は商上の射の合成。 -/
lemma freeBlockQuotientInputMap_comp (F : SymmetricSequence C) (n : ℕ) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    freeBlockQuotientInputMap F n (f ≫ g) m =
      freeBlockQuotientInputMap F n f m ≫ freeBlockQuotientInputMap F n g m := by
  apply freeBlockQuotient_hom_ext
  intro h
  simp only [freeBlockQuotientGenerator_input, freeBlockQuotientGenerator_input_assoc,
    whiskerLeft_comp, Category.assoc]

/-- 商上の入力の射と出力の全単射は可換。 -/
@[reassoc] lemma freeBlockQuotientInputMap_output (F : SymmetricSequence C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (m : ℕ) (k : FiniteBijection.of m ⟶ FiniteBijection.of m) :
    freeBlockQuotientInputMap F n f m ≫ freeBlockQuotientOutputMap F n Y m k =
      freeBlockQuotientOutputMap F n X m k ≫ freeBlockQuotientInputMap F n f m := by
  apply freeBlockQuotient_hom_ext
  intro h
  simp only [freeBlockQuotientGenerator_input_assoc, freeBlockQuotientGenerator_output,
    freeBlockQuotientGenerator_output_assoc, freeBlockQuotientGenerator_input]

variable [MonoidalClosed C]

/-- 各段と商との比較同型は出力の全単射と両立する。 -/
@[reassoc] lemma freeConvolutionLevelIsoBlockQuotient_output
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m) :
    (convolution F ((freeAt n).obj X)).map k ≫
        (freeConvolutionLevelIsoBlockQuotient F n X m).hom =
      (freeConvolutionLevelIsoBlockQuotient F n X m).hom ≫
        freeBlockQuotientOutputMap F n X m k := by
  apply freeConvolutionLevel_hom_ext_standard
  intro h
  rw [← Category.assoc, freeConvolutionGenerator_map,
    freeConvolutionLevelIsoBlockQuotient_generator]
  rw [freeConvolutionLevelIsoBlockQuotient_generator_assoc]
  simpa only [freeBlockQuotientGenerator, Category.assoc] using
    (freeBlockQuotientGenerator_output F n X m k h).symm

/-- 各段と商との比較同型は入力の射と両立する。 -/
@[reassoc] lemma freeConvolutionLevelIsoBlockQuotient_input
    (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    (freeConvolutionInputMap F n f).app (FiniteBijection.of m) ≫
        (freeConvolutionLevelIsoBlockQuotient F n Y m).hom =
      (freeConvolutionLevelIsoBlockQuotient F n X m).hom ≫ freeBlockQuotientInputMap F n f m := by
  apply freeConvolutionLevel_hom_ext_standard
  intro h
  rw [← Category.assoc, freeConvolutionGenerator_input, Category.assoc,
    freeConvolutionLevelIsoBlockQuotient_generator]
  rw [freeConvolutionLevelIsoBlockQuotient_generator_assoc]
  simpa only [freeBlockQuotientGenerator, Category.assoc] using
    (freeBlockQuotientGenerator_input F n f m h).symm

end SerrePositivity.SymmetricSequence
