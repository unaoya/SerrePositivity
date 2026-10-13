module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInduction

/-! # 自由convolutionの誘導表示の自然性

出力の全単射は誘導図式の添字へ後合成し、入力の射は各項の第二因子へ作用する。
これらの余極限上の射と、自由convolutionの射を比較する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C]

/-- 出力の全単射による、誘導図式の余極限への余錐。 -/
def freeInductionOutputCocone (F : SymmetricSequence C) (n : ℕ) (X : C) {m m' : ℕ}
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    Cocone (freeInductionDiagram F n X m) where
  pt := colimit (freeInductionDiagram F n X m')
  ι.app d := colimit.ι (freeInductionDiagram F n X m') ((CostructuredArrow.map k).obj d)
  ι.naturality d e φ := by
    change (freeInductionDiagram F n X m').map ((CostructuredArrow.map k).map φ) ≫
      colimit.ι (freeInductionDiagram F n X m') ((CostructuredArrow.map k).obj e) =
        colimit.ι (freeInductionDiagram F n X m') ((CostructuredArrow.map k).obj d) ≫ 𝟙 _
    rw [Category.comp_id]
    exact colimit.w _ _

/-- 出力の全単射を、添字への後合成として余極限へ延長する。 -/
def freeInductionOutputMap (F : SymmetricSequence C) (n : ℕ) (X : C) {m m' : ℕ}
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    colimit (freeInductionDiagram F n X m) ⟶ colimit (freeInductionDiagram F n X m') :=
  colimit.desc _ (freeInductionOutputCocone F n X k)

omit [MonoidalClosed C] in
/-- 出力の射は包含の全単射の添字へ後合成する。 -/
@[reassoc (attr := simp)] lemma freeInductionOutputMap_inclusion
    (F : SymmetricSequence C) (n : ℕ) (X : C) {m m' : ℕ}
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m')
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeInductionDiagram F n X m) d ≫ freeInductionOutputMap F n X k =
      colimit.ι (freeInductionDiagram F n X m') ((CostructuredArrow.map k).obj d) :=
  colimit.ι_desc (freeInductionOutputCocone F n X k) d

/-- 誘導表示の比較同型は出力の全単射と両立する。 -/
@[reassoc] lemma freeConvolutionLevelIsoInduction_output
    (F : SymmetricSequence C) (n : ℕ) (X : C) {m m' : ℕ}
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    (convolution F ((freeAt n).obj X)).map k ≫
        (freeConvolutionLevelIsoInduction F n X m').hom =
      (freeConvolutionLevelIsoInduction F n X m).hom ≫ freeInductionOutputMap F n X k := by
  apply freeConvolutionLevel_hom_ext
  intro a h
  erw [freeConvolutionGenerator_map_assoc,
    freeConvolutionLevelIsoInduction_generator F n X m' (CostructuredArrow.mk (Y := a) (h ≫ k))]
  erw [freeConvolutionLevelIsoInduction_generator_assoc F n X m
    (CostructuredArrow.mk (Y := a) h), freeInductionOutputMap_inclusion]
  rfl

/-- 入力の射は誘導図式の第二因子へ作用する。 -/
def freeInductionInputTransformation (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) : freeInductionDiagram F n X m ⟶ freeInductionDiagram F n Y m where
  app d := F.obj d.left ◁ f
  naturality _ _ φ := (whisker_exchange (F.map φ.left) f).symm

/-- 入力の射が誘導図式の余極限へ誘導する射。 -/
def freeInductionInputMap (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) :
    colimit (freeInductionDiagram F n X m) ⟶ colimit (freeInductionDiagram F n Y m) :=
  colim.map (freeInductionInputTransformation F n f m)

omit [MonoidalClosed C] in
/-- 入力の射は包含の第二因子へ作用する。 -/
@[reassoc (attr := simp)] lemma freeInductionInputMap_inclusion
    (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeInductionDiagram F n X m) d ≫ freeInductionInputMap F n f m =
      F.obj d.left ◁ f ≫ colimit.ι (freeInductionDiagram F n Y m) d :=
  colimit.ι_map (freeInductionInputTransformation F n f m) d

/-- 自由convolutionが入力の射へ作用する自然変換。 -/
def freeConvolutionInputMap (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    convolution F ((freeAt n).obj X) ⟶ convolution F ((freeAt n).obj Y) :=
  convolutionFunctor.map (𝟙 F, (freeAt n).map f)

omit [MonoidalClosed C] in
/-- 入力の射と、自由convolutionの生成元との両立。 -/
@[reassoc] lemma freeConvolutionGenerator_input (F : SymmetricSequence C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (m : ℕ) (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    freeConvolutionGenerator F n X m a h ≫ (freeConvolutionInputMap F n f).app
        (FiniteBijection.of m) =
      F.obj a ◁ f ≫ freeConvolutionGenerator F n Y m a h := by
  let η : externalProduct F ((freeAt n).obj X) ⟶ externalProduct F ((freeAt n).obj Y) :=
    (externalProductBifunctor FiniteBijection FiniteBijection C).map
      (𝟙 (toFunctorCategory.obj F), toFunctorCategory.map ((freeAt n).map f))
  have hn := congr_app (FiniteBijection.sumFunctor.lanUnit.naturality η)
    (a, FiniteBijection.of n)
  change η.app (a, FiniteBijection.of n) ≫
      (convolutionUnit F ((freeAt n).obj Y)).app (a, FiniteBijection.of n) =
    (convolutionUnit F ((freeAt n).obj X)).app (a, FiniteBijection.of n) ≫
      (freeConvolutionInputMap F n f).app (FiniteBijection.sumObj a (FiniteBijection.of n)) at hn
  have hg : freeAtGenerator n X ≫ ((freeAt n).map f).app (FiniteBijection.of n) =
      f ≫ freeAtGenerator n Y :=
    freeAtInclusion_map_input n f (𝟙 (FiniteBijection.of n))
  simp only [freeConvolutionGenerator, Category.assoc]
  erw [(freeConvolutionInputMap F n f).naturality h, ← reassoc_of% hn]
  change F.obj a ◁ freeAtGenerator n X ≫
      ((𝟙 (F.obj a) ▷ _) ≫ F.obj a ◁ ((freeAt n).map f).app (FiniteBijection.of n)) ≫ _ = _
  simp only [id_whiskerRight, Category.id_comp]
  rw [← whiskerLeft_comp_assoc, hg]
  simp only [whiskerLeft_comp, Category.assoc]

/-- 誘導表示の比較同型は入力の射と両立する。 -/
@[reassoc] lemma freeConvolutionLevelIsoInduction_input
    (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    (freeConvolutionInputMap F n f).app (FiniteBijection.of m) ≫
        (freeConvolutionLevelIsoInduction F n Y m).hom =
      (freeConvolutionLevelIsoInduction F n X m).hom ≫ freeInductionInputMap F n f m := by
  apply freeConvolutionLevel_hom_ext
  intro a h
  rw [← Category.assoc, freeConvolutionGenerator_input, Category.assoc]
  erw [freeConvolutionLevelIsoInduction_generator F n Y m
    (CostructuredArrow.mk (Y := a) h)]
  erw [freeConvolutionLevelIsoInduction_generator_assoc F n X m
    (CostructuredArrow.mk (Y := a) h), freeInductionInputMap_inclusion]
  rfl

omit [MonoidalClosed C] in
/-- 恒等全単射は誘導表示上の恒等射。 -/
@[simp] lemma freeInductionOutputMap_id (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeInductionOutputMap F n X (𝟙 (FiniteBijection.of m)) = 𝟙 _ := by
  apply colimit.hom_ext
  intro d
  rw [CostructuredArrow.eq_mk d]
  simp only [freeInductionOutputMap_inclusion, CostructuredArrow.map_mk, Category.comp_id]
  exact congrArg (fun h : (FiniteBijection.addRight n).obj d.left ⟶ FiniteBijection.of m =>
    (show F.obj d.left ⊗ X ⟶ colimit (freeInductionDiagram F n X m) from
      colimit.ι (freeInductionDiagram F n X m) (CostructuredArrow.mk (Y := d.left) h)))
      (Category.comp_id d.hom)

omit [MonoidalClosed C] in
/-- 出力の全単射の合成は、余極限上の射の合成。 -/
lemma freeInductionOutputMap_comp (F : SymmetricSequence C) (n : ℕ) (X : C)
    {m m' m'' : ℕ} (k : FiniteBijection.of m ⟶ FiniteBijection.of m')
    (l : FiniteBijection.of m' ⟶ FiniteBijection.of m'') :
    freeInductionOutputMap F n X (k ≫ l) =
      freeInductionOutputMap F n X k ≫ freeInductionOutputMap F n X l := by
  apply colimit.hom_ext
  intro d
  rw [CostructuredArrow.eq_mk d]
  simp only [freeInductionOutputMap_inclusion, freeInductionOutputMap_inclusion_assoc,
    CostructuredArrow.map_mk]
  exact congrArg (fun h : (FiniteBijection.addRight n).obj d.left ⟶ FiniteBijection.of m'' =>
    (show F.obj d.left ⊗ X ⟶ colimit (freeInductionDiagram F n X m'') from
      colimit.ι (freeInductionDiagram F n X m'') (CostructuredArrow.mk (Y := d.left) h)))
      (Category.assoc d.hom k l).symm

omit [MonoidalClosed C] in
/-- 入力の恒等射は誘導表示上の恒等射。 -/
@[simp] lemma freeInductionInputMap_id (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeInductionInputMap F n (𝟙 X) m = 𝟙 _ := by
  apply colimit.hom_ext
  intro d
  simp only [freeInductionInputMap_inclusion, whiskerLeft_id, Category.id_comp, Category.comp_id]

omit [MonoidalClosed C] in
/-- 入力の射の合成は、余極限上の射の合成。 -/
lemma freeInductionInputMap_comp (F : SymmetricSequence C) (n : ℕ) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    freeInductionInputMap F n (f ≫ g) m =
      freeInductionInputMap F n f m ≫ freeInductionInputMap F n g m := by
  apply colimit.hom_ext
  intro d
  simp only [freeInductionInputMap_inclusion, freeInductionInputMap_inclusion_assoc,
    whiskerLeft_comp, Category.assoc]

omit [MonoidalClosed C] in
/-- 入力の射と出力の全単射は誘導表示上で可換。 -/
@[reassoc] lemma freeInductionInputMap_output (F : SymmetricSequence C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) {m m' : ℕ}
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    freeInductionInputMap F n f m ≫ freeInductionOutputMap F n Y k =
      freeInductionOutputMap F n X k ≫ freeInductionInputMap F n f m' := by
  apply colimit.hom_ext
  intro d
  simp only [freeInductionInputMap_inclusion_assoc, freeInductionOutputMap_inclusion,
    freeInductionOutputMap_inclusion_assoc, freeInductionInputMap_inclusion]
  rfl

end SerrePositivity.SymmetricSequence
