module

public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Module.ConeShiftSquares
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import SerrePositivity.DifferentialGraded.Module.GradedSplitHomExact
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Functor.HomIso
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.HomWhisker
public import Mathlib.CategoryTheory.Enriched.HomCongr
public import SerrePositivity.DifferentialGraded.Module.Precomposition
public import SerrePositivity.DifferentialGraded.Functor.ModuleShiftOpposite
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit

/-!
# Endomorphism.Shift

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarGradedSplit（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarGradedSplit.lean） -/

/-! # 実際の加群係数拡大は全次数分裂を保存する -/

@[expose] public section ScalarGradedSplit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomElement_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleHomElement φ D (endomorphismClosedElement A D f) =
      endomorphismClosedElement A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) :=
  scalarModuleHomElement_cycle φ D f

/-- 環の平坦性を要求せず、全斉次作用に関して分裂する拡大を送る。 -/
def scalarModuleGradedSplit {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) :
    ModuleGradedSplit A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f)
      ((ScalarExtension.moduleExtension φ D).map g) := by
  have hfa := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_inclusion_retraction_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed] at hfa
  have hbg := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_section_projection_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed] at hbg
  have hba := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_section_retraction_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_zero] at hba
  have hdec := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_decomposition_element s)
  rw [scalarModuleHomElement_add, scalarModuleHomElement_forward,
    scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed, scalarModuleHomElement_closed] at hdec
  exact moduleGradedSplitOfHomElements A' (ScalarExtension.DGBaseChange φ D)
    ((ScalarExtension.moduleExtension φ D).map f) ((ScalarExtension.moduleExtension φ D).map g)
    (scalarModuleHomElement φ D s.retractionElement)
    (scalarModuleHomElement φ D s.sectionElement)
    hfa hbg hba hdec (by
      rw [← Functor.map_comp, s.inclusion_projection, Functor.map_zero])

end SerrePositivity.DifferentialGraded
end

end ScalarGradedSplit

/-! ## ScalarModuleConeImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleConeImage.lean） -/

/-! # 実際の加群係数拡大と標準coneの比較同型 -/

@[expose] public section ScalarModuleConeImage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarModuleConeInl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  scalarModuleHomElement φ D (moduleConeInlElement A D f)

lemma scalarModuleConeInl_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
      (scalarModuleConeInl φ D f) =
    endomorphismClosedElement A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f ≫
        (ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f)) := by
  rw [scalarModuleConeInl, scalarModuleHomElement_d, moduleConeInlElement_d]
  have h := scalarModuleHomElement_closed φ D (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at h
  exact h

def scalarModuleExtensionConeComparison {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A' (ScalarExtension.DGBaseChange φ D) ((ScalarExtension.moduleExtension φ D).map f) ⟶
      (ScalarExtension.moduleExtension φ D).obj (moduleCone A D f) :=
  moduleConeDescOfBoundary A' (ScalarExtension.DGBaseChange φ D)
    ((ScalarExtension.moduleExtension φ D).map f) (scalarModuleConeInl φ D f)
    ((ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f))
    (scalarModuleConeInl_d φ D f)

instance scalarModuleExtensionConeComparison_isIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso (scalarModuleExtensionConeComparison φ D f) := by
  apply moduleIsIso_of_evaluations A' (ScalarExtension.DGBaseChange φ D)
  intro x
  rw [scalarModuleExtensionConeComparison, moduleConeDescOfBoundary_eval]
  let L := ModuleCat.extendScalars φ
  let g := (moduleEvaluation A D (show D from x)).map f
  have hα := scalarModuleHomElement_π_map φ D (moduleConeInlElement A D f) (show D from x)
  rw [moduleConeInlElement_π] at hα
  have hβ := ScalarExtension.moduleExtension_eval φ D (moduleConeInr A D f) x
  rw [moduleConeInr_eval] at hβ
  apply complexConeDesc_isIso A' _ _ _ ((mappingCone.fst g).val.map L) ((mappingCone.snd g).map L)
  · apply (congrArg (fun z => z.comp ((mappingCone.fst g).val.map L) (neg_add_cancel 1)) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inl_fst g)
  · apply (congrArg (fun z => z.comp ((mappingCone.snd g).map L) (add_zero (-1))) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inl_snd g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inr_fst g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inr_snd g)
  · let X' := (ScalarExtension.extension φ).obj ((moduleEvaluation A D (show D from x)).obj M)
    let Y' := (ScalarExtension.extension φ).obj ((moduleEvaluation A D (show D from x)).obj N)
    let K' := (ScalarExtension.extension φ).obj (mappingCone g)
    apply (congrArg₂ (fun (a : Cochain X' K' (-1)) (b : Y' ⟶ K') =>
      ((mappingCone.fst g).val.map L).comp a (add_neg_cancel 1) +
      ((mappingCone.snd g).map L).comp (Cochain.ofHom b) (add_zero 0)) hα hβ).trans
    simpa only [Cochain.map_add, Cochain.map_comp, Cochain.map_ofHom,
      CategoryTheory.Functor.map_id] using congrArg (fun z => z.map L) (mappingCone.id g)

def scalarModuleExtensionConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A' (ScalarExtension.DGBaseChange φ D) ((ScalarExtension.moduleExtension φ D).map f) ≅
      (ScalarExtension.moduleExtension φ D).obj (moduleCone A D f) :=
  asIso (scalarModuleExtensionConeComparison φ D f)

@[reassoc] lemma scalarModuleExtensionConeComparison_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) ≫ scalarModuleExtensionConeComparison φ D f =
      (ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f) :=
  moduleConeDescOfBoundary_inr A' (ScalarExtension.DGBaseChange φ D) _ _ _ _

end SerrePositivity.DifferentialGraded
end

end ScalarModuleConeImage

/-! ## ShiftNormalization（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftNormalization.lean） -/

/-! # 整合的shift比較のための斉次射影の符号正規化

MathlibのleftShiftに含まれる定数符号を明示的に除く。
既存の比較同型を変更せず、正規化した比較を別に構成する。
-/

@[expose] public section ShiftNormalization
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleShiftNormalizationExponent (s : ℤ) : ℤ := s * s + s * (s - 1) / 2

/-- 評価成分が恒等射となる次数sの射影。 -/
def normalizedModuleShiftOut (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).X s :=
  (moduleShiftNormalizationExponent s).negOnePow • moduleShiftOutElement A D s M

lemma normalizedModuleShiftOut_π (s : ℤ) (M : RightModule A D) (x : D) :
    (moduleHomπ A D (shiftModule s M) M x).f s (normalizedModuleShiftOut A D s M) =
      (moduleShiftNormalizationExponent s).negOnePow •
        (Cochain.ofHom (𝟙 (M.obj (op x)))).leftShift s s (zero_add s) := by
  simp only [normalizedModuleShiftOut, Units.smul_def, map_zsmul, moduleShiftOutElement_π]

lemma normalizedModuleShiftOut_v (s : ℤ) (M : RightModule A D) (x : D) (i : ℤ) :
    ((moduleHomπ A D (shiftModule s M) M x).f s (normalizedModuleShiftOut A D s M)).v
        i (i + s) rfl = 𝟙 _ := by
  rw [normalizedModuleShiftOut_π, Cochain.units_smul_v,
    Cochain.leftShift_v _ s s (zero_add s) i (i + s) rfl (i + s) (add_zero _)]
  simp only [Cochain.ofHom_v, id_f, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id, moduleShiftNormalizationExponent,
    smul_smul, Int.units_mul_self, one_smul]
  rfl

lemma normalizedModuleShiftOut_d (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).d s (s + 1) (normalizedModuleShiftOut A D s M) = 0 := by
  simp only [normalizedModuleShiftOut, Units.smul_def, map_zsmul, moduleShiftOutElement_d,
    zsmul_zero]

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- 既存の加群shift同型を、定数符号を除いた同型として正規化する。 -/
def normalizedDGModuleFunctorShiftIso (s : ℤ) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (F.obj (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A) (shiftModule s (F.obj M)) :=
  dgModuleFunctorShiftIso A B D F s M ≪≫
    moduleShiftSignIso A B (moduleShiftNormalizationExponent s)
      (ForgetEnrichment.of (Complex A) (shiftModule s (F.obj M)))

lemma normalizedDGModuleFunctorShiftIso_hom_eval_f (s : ℤ) (M : RightModule A D)
    (b : B) (i : ℤ) :
    ((moduleEvaluation A B b).map (normalizedDGModuleFunctorShiftIso A D B F s M).hom).f i =
      ((moduleHomπ A B (F.obj (shiftModule s M)) (F.obj M) b).f s
        ((F.map (shiftModule s M) M).f s (normalizedModuleShiftOut A D s M))).v i (i + s) rfl := by
  unfold normalizedDGModuleFunctorShiftIso
  rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, dgModuleFunctorShiftIso_hom_eval]
  change _ ≫ ((moduleEvaluation A B b).map
    ((moduleShiftNormalizationExponent s).negOnePow • 𝟙 _)).f i = _
  rw [moduleEvaluation_sign_map, CategoryTheory.Functor.map_id]
  simp only [HomologicalComplex.units_smul_f_apply, id_f]
  change (DGFunctor.moduleShiftImageComparison A D (F.comp (moduleEvaluationDG A B b)) s M).f i ≫
    ((moduleShiftNormalizationExponent s).negOnePow •
      𝟙 (((CategoryTheory.shiftFunctor (Complex A) s).obj
        ((F.comp (moduleEvaluationDG A B b)).obj M)).X i)) = _
  rw [Linear.comp_units_smul, Category.comp_id, DGFunctor.moduleShiftImageComparison_f]
  simp only [normalizedModuleShiftOut, Units.smul_def, map_zsmul]
  rfl

lemma normalizedDGModuleFunctorShiftIso_id (s : ℤ) (M : RightModule A D) :
    normalizedDGModuleFunctorShiftIso A D D (DGFunctor.id (RightModule A D)) s M =
      Iso.refl _ := by
  apply Iso.ext
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  rw [normalizedDGModuleFunctorShiftIso_hom_eval_f]
  have hi := congrArg (fun k => k.f i) ((moduleEvaluation A D b).map_id
    (ForgetEnrichment.of (Complex A) (shiftModule s M)))
  exact (normalizedModuleShiftOut_v A D s M b i).trans hi.symm

end SerrePositivity.DifferentialGraded
end

end ShiftNormalization

/-! ## ShiftNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftNaturality.lean） -/

/-! # 正規化したshift比較の閉零射自然性 -/

@[expose] public section ShiftNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    forward A (x := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (y := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (z := ForgetEnrichment.to (Complex A) N)
      (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f))
      (normalizedModuleShiftOut A D s (ForgetEnrichment.to (Complex A) N)) (zero_add s) =
    forward A (x := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) N)
      (normalizedModuleShiftOut A D s (ForgetEnrichment.to (Complex A) M))
      (endomorphismClosedElement A D f) (add_zero s) := by
  apply moduleHomElement_ext A D
  intro x
  have hs : (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0
        (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) =
      Cochain.ofHom ((moduleEvaluation A D x).map ((moduleShiftFunctor A D s).map f)) :=
    endomorphismClosedElement_π A D ((moduleShiftFunctor A D s).map f) x
  rw [moduleHomForward_π, moduleHomForward_π, hs, endomorphismClosedElement_π]
  simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  subst j
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    normalizedModuleShiftOut_v, normalizedModuleShiftOut_v]
  simp only [Cochain.ofHom_v, Category.comp_id, Category.id_comp]
  change (((moduleEvaluation A D x).map (moduleShiftMap A D s f)).f i) = _
  rw [moduleShiftMap_eval]
  rfl

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftIso_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    F.onClosed.map ((moduleShiftFunctor A D s).map f) ≫
        (normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) N)).hom =
      (normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) M)).hom ≫
        (moduleShiftFunctor A B s).map (F.onClosed.map f) := by
  have h := congrArg (fun z => (F.map
    (shiftModule s (ForgetEnrichment.to (Complex A) M))
    (ForgetEnrichment.to (Complex A) N)).f s z)
      (normalizedModuleShiftOut_naturality A D s f)
  rw [F.map_forward A, F.map_forward A] at h
  have hs : (F.map (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).f 0
        (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) =
      endomorphismClosedElement A B (F.onClosed.map ((moduleShiftFunctor A D s).map f)) :=
    dgModuleFunctor_closedElement A D B F ((moduleShiftFunctor A D s).map f)
  rw [hs, dgModuleFunctor_closedElement] at h
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  have hv := congrArg (fun z => ((moduleHomπ A B
    (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) M)))
    (F.obj (ForgetEnrichment.to (Complex A) N)) b).f s z).v i (i + s) rfl) h
  rw [moduleHomForward_π, moduleHomForward_π] at hv
  simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul] at hv
  have hπs : (moduleHomπ A B
      (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) M)))
      (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) N))) b).f 0
        (endomorphismClosedElement A B (F.onClosed.map ((moduleShiftFunctor A D s).map f))) =
      Cochain.ofHom ((moduleEvaluation A B b).map
        (F.onClosed.map ((moduleShiftFunctor A D s).map f))) :=
    endomorphismClosedElement_π A B (F.onClosed.map ((moduleShiftFunctor A D s).map f)) b
  have hπ : (moduleHomπ A B (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) N)) b).f 0
        (endomorphismClosedElement A B (F.onClosed.map f)) =
      Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map f)) :=
    endomorphismClosedElement_π A B (F.onClosed.map f) b
  erw [hπs, hπ,
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v] at hv
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  change _ = _ ≫ (((moduleEvaluation A B b).map
    (moduleShiftMap A B s (F.onClosed.map f))).f i)
  rw [moduleShiftMap_eval]
  exact hv

/-- 正規化shift比較を閉零加群圏の自然同型に組み立てる。 -/
def normalizedDGModuleFunctorShiftNatIso (s : ℤ) :
    moduleShiftFunctor A D s ⋙ F.onClosed ≅ F.onClosed ⋙ moduleShiftFunctor A B s :=
  NatIso.ofComponents
    (fun M => normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) M))
    (fun f => normalizedDGModuleFunctorShiftIso_naturality A D B F s f)

end SerrePositivity.DifferentialGraded
end

end ShiftNaturality

/-! ## ShiftZeroCoherence（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftZeroCoherence.lean） -/

/-! # 正規化shift比較と零shiftの整合性 -/

@[expose] public section ShiftZeroCoherence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_zero (M : RightModule A D) :
    normalizedModuleShiftOut A D 0 M =
      endomorphismClosedElement A D (moduleShiftZeroIsoObj A D M).hom := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (shiftModule 0 M) M x).f 0
      (endomorphismClosedElement A D (moduleShiftZeroIsoObj A D M).hom) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).hom) :=
    endomorphismClosedElement_π A D (moduleShiftZeroIsoObj A D M).hom x
  erw [hπ]
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, moduleShiftZeroIsoObj_hom_eval, shiftFunctorZero_hom_app_f]
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + 0) i rfl (add_zero i),
    normalizedModuleShiftOut_v, Category.id_comp]

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftNatIso_zero :
    normalizedDGModuleFunctorShiftNatIso A D B F 0 =
      CategoryTheory.Functor.CommShift.isoZero F.onClosed ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  change ((moduleEvaluation A B b).map
    (normalizedDGModuleFunctorShiftIso A D B F 0 (ForgetEnrichment.to (Complex A) M)).hom).f i = _
  rw [normalizedDGModuleFunctorShiftIso_hom_eval_f, normalizedModuleShiftOut_zero]
  have hm : (F.map (shiftModule 0 (ForgetEnrichment.to (Complex A) M))
      (ForgetEnrichment.to (Complex A) M)).f 0
      (endomorphismClosedElement A D
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom) =
      endomorphismClosedElement A B (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom) :=
    dgModuleFunctor_closedElement A D B F _
  erw [hm]
  have hπ : (moduleHomπ A B (F.obj (shiftModule 0 (ForgetEnrichment.to (Complex A) M)))
      (F.obj (ForgetEnrichment.to (Complex A) M)) b).f 0
      (endomorphismClosedElement A B (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)) =
      Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)) :=
    endomorphismClosedElement_π A B _ b
  erw [hπ]
  change (Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map
    (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom))).v i (i + 0) rfl = _
  rw [← Cochain.v_comp_XIsoOfEq_inv _ i i (i + 0) (add_zero i) (add_zero i),
    Cochain.ofHom_v]
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app,
    CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  change _ =
    ((moduleEvaluation A B b).map (F.onClosed.map
      (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)).f i ≫
      ((moduleEvaluation A B b).map
        (moduleShiftZeroIsoObj A B (F.obj (ForgetEnrichment.to (Complex A) M))).inv).f i
  rw [moduleShiftZeroIsoObj_inv_eval, shiftFunctorZero_inv_app_f]
  rfl

end SerrePositivity.DifferentialGraded
end

end ShiftZeroCoherence

/-! ## ShiftAdditionElements（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftAdditionElements.lean） -/

/-! # 正規化斉次射影と加法shiftの合成 -/

@[expose] public section ShiftAdditionElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_v_eq (s : ℤ) (M : RightModule A D) (x : D)
    (i j : ℤ) (hij : i + s = j) :
    ((moduleHomπ A D (shiftModule s M) M x).f s (normalizedModuleShiftOut A D s M)).v
        i j hij = ((M.obj (op x)).XIsoOfEq hij).hom := by
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + s) j rfl hij,
    normalizedModuleShiftOut_v, Category.id_comp]

lemma normalizedModuleShiftOut_add (s t : ℤ) (M : RightModule A D) :
    forward A (x := shiftModule (s + t) M) (y := shiftModule t (shiftModule s M)) (z := M)
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom)
      (compose A (x := shiftModule t (shiftModule s M)) (y := shiftModule s M) (z := M)
        (normalizedModuleShiftOut A D s M)
        (normalizedModuleShiftOut A D t (shiftModule s M)) (add_comm t s))
      (zero_add (s + t)) = normalizedModuleShiftOut A D (s + t) M := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (shiftModule (s + t) M) (shiftModule t (shiftModule s M)) x).f 0
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).hom) :=
    endomorphismClosedElement_π A D (moduleShiftAddIsoObj A D s t M).hom x
  rw [moduleHomForward_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  erw [hπ]
  simp only [compose, Units.smul_def, map_zsmul]
  rw [moduleHomForward_π]
  simp only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v,
    Cochain.comp_v _ _ _ i (i + t) j rfl (by omega),
    normalizedModuleShiftOut_v, normalizedModuleShiftOut_v_eq,
    normalizedModuleShiftOut_v_eq, Cochain.ofHom_v, moduleShiftAddIsoObj_hom_eval,
    shiftFunctorAdd_hom_app_f, Category.id_comp]
  change ((M.obj (op x)).XIsoOfEq _).hom ≫ ((M.obj (op x)).XIsoOfEq _).hom =
    ((M.obj (op x)).XIsoOfEq _).hom
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

end SerrePositivity.DifferentialGraded
end

end ShiftAdditionElements

/-! ## ShiftAddCoherence（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftAddCoherence.lean） -/

/-! # 正規化shift比較と加法shiftの整合性 -/

@[expose] public section ShiftAddCoherence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftIso_add_square (s t : ℤ) (M : RightModule A D) :
    F.onClosed.map (moduleShiftAddIsoObj A D s t M).hom ≫
        (normalizedDGModuleFunctorShiftIso A D B F t (shiftModule s M)).hom ≫
        (moduleShiftFunctor A B t).map (normalizedDGModuleFunctorShiftIso A D B F s M).hom =
      (normalizedDGModuleFunctorShiftIso A D B F (s + t) M).hom ≫
        (moduleShiftAddIsoObj A B s t (F.obj M)).hom := by
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  let G := F.comp (moduleEvaluationDG A B b)
  have h := congrArg (fun z => (G.map (shiftModule (s + t) M) M).f (s + t) z)
    (normalizedModuleShiftOut_add A D s t M)
  rw [G.map_forward_cochain A, G.map_compose_cochain A] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  have hc : (G.map (shiftModule (s + t) M) (shiftModule t (shiftModule s M))).f 0
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom) =
      Cochain.ofHom ((G.toComplexFunctor A).map (moduleShiftAddIsoObj A D s t M).hom) :=
    G.map_closedElement A (moduleShiftAddIsoObj A D s t M).hom
  rw [hc] at h
  have hv := Cochain.congr_v h i ((i + t) + s) (by omega)
  rw [Cochain.zero_cochain_comp_v,
    Cochain.comp_v _ _ _ i (i + t) ((i + t) + s) rfl rfl,
    Cochain.ofHom_v] at hv
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + (s + t)) ((i + t) + s) rfl (by omega)] at hv
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    moduleShiftAddIsoObj_hom_eval, shiftFunctorAdd_hom_app_f]
  change _ ≫ (_ ≫ (((moduleEvaluation A B b).map
    (moduleShiftMap A B t (normalizedDGModuleFunctorShiftIso A D B F s M).hom)).f i)) = _
  rw [moduleShiftMap_eval]
  change _ ≫ (_ ≫ ((moduleEvaluation A B b).map
    (normalizedDGModuleFunctorShiftIso A D B F s M).hom).f (i + t)) = _
  rw [normalizedDGModuleFunctorShiftIso_hom_eval_f]
  exact hv

lemma shiftComparison_eq_isoAdd_of_square {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] (H : C ⥤ E) (s t : ℤ)
    (es : CategoryTheory.shiftFunctor C s ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E s)
    (et : CategoryTheory.shiftFunctor C t ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E t)
    (est : CategoryTheory.shiftFunctor C (s + t) ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E (s + t))
    (h : ∀ X, H.map ((shiftFunctorAdd C s t).hom.app X) ≫
      et.hom.app ((CategoryTheory.shiftFunctor C s).obj X) ≫
      (CategoryTheory.shiftFunctor E t).map (es.hom.app X) =
        est.hom.app X ≫ (shiftFunctorAdd E s t).hom.app (H.obj X)) :
    est = CategoryTheory.Functor.CommShift.isoAdd es et := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rw [CategoryTheory.Functor.CommShift.isoAdd_hom_app]
  rw [← cancel_mono ((shiftFunctorAdd E s t).hom.app (H.obj X))]
  simp only [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.comp_obj, Category.comp_id]
  exact (h X).symm

/-- 登録済みshiftの型へ、関手の等式を明示的に用いて移す。 -/
def normalizedDGModuleFunctorCommShiftIso (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s ⋙ F.onClosed ≅
      F.onClosed ⋙ CategoryTheory.shiftFunctor (ModuleCategory A B) s := by
  rw [moduleShiftFunctor_eq, moduleShiftFunctor_eq]
  exact normalizedDGModuleFunctorShiftNatIso A D B F s

lemma normalizedDGModuleFunctorCommShiftIso_zero :
    normalizedDGModuleFunctorCommShiftIso A D B F 0 =
      CategoryTheory.Functor.CommShift.isoZero F.onClosed ℤ := by
  exact normalizedDGModuleFunctorShiftNatIso_zero A D B F

lemma normalizedDGModuleFunctorShiftNatIso_add (s t : ℤ) :
    normalizedDGModuleFunctorCommShiftIso A D B F (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A B) (A := ℤ)
        (F := F.onClosed) (a := s) (b := t)
        (normalizedDGModuleFunctorCommShiftIso A D B F s)
        (normalizedDGModuleFunctorCommShiftIso A D B F t) := by
  apply shiftComparison_eq_isoAdd_of_square
    (C := ModuleCategory A D) (E := ModuleCategory A B) F.onClosed s t
    (normalizedDGModuleFunctorCommShiftIso A D B F s)
    (normalizedDGModuleFunctorCommShiftIso A D B F t)
    (normalizedDGModuleFunctorCommShiftIso A D B F (s + t))
  intro M
  simp only [moduleShiftAdd_eq, moduleShiftFunctor_eq,
    normalizedDGModuleFunctorCommShiftIso]
  exact normalizedDGModuleFunctorShiftIso_add_square A D B F s t
    (ForgetEnrichment.to (Complex A) M)

/-- 加群値dg関手の閉零関手は、正規化比較で整数shiftと整合的に可換する。 -/
@[instance_reducible]
def dgModuleFunctorCommShift : F.onClosed.CommShift ℤ where
  commShiftIso := normalizedDGModuleFunctorCommShiftIso A D B F
  commShiftIso_zero := normalizedDGModuleFunctorCommShiftIso_zero A D B F
  commShiftIso_add := normalizedDGModuleFunctorShiftNatIso_add A D B F

end SerrePositivity.DifferentialGraded
end

end ShiftAddCoherence

/-! ## ShortExactComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShortExactComparison.lean） -/

/-! # Hom複体の短完全列の比較に用いる中央項の五項補題 -/

@[expose] public section ShortExactComparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex ComposableArrows

lemma complexQuasiIso_middle_of_shortExact {A : Type u} [CommRing A]
    {S₁ S₂ : ShortComplex (Complex A)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have := h₁
  have := h₃
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hp : (ComplexShape.up ℤ).Rel (q - 1) q := ComplexShape.up_mk _ _ (by omega)
  have hn : (ComplexShape.up ℤ).Rel q (q + 1) := ComplexShape.up_mk _ _ rfl
  let R₁ := mk₄ (hS₁.δ (q - 1) q hp) (homologyMap S₁.f q)
    (homologyMap S₁.g q) (hS₁.δ q (q + 1) hn)
  let R₂ := mk₄ (hS₂.δ (q - 1) q hp) (homologyMap S₂.f q)
    (homologyMap S₂.g q) (hS₂.δ q (q + 1) hn)
  have he₁ : R₁.Exact := exact_of_δ₀
    (hS₁.homology_exact₁ (q - 1) q hp).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₂ q).exact_toComposableArrows
      (hS₁.homology_exact₃ q (q + 1) hn).exact_toComposableArrows)
  have he₂ : R₂.Exact := exact_of_δ₀
    (hS₂.homology_exact₁ (q - 1) q hp).exact_toComposableArrows
    (exact_of_δ₀ (hS₂.homology_exact₂ q).exact_toComposableArrows
      (hS₂.homology_exact₃ q (q + 1) hn).exact_toComposableArrows)
  let ψ : R₁ ⟶ R₂ := homMk₄ (homologyMap φ.τ₃ (q - 1)) (homologyMap φ.τ₁ q)
    (homologyMap φ.τ₂ q) (homologyMap φ.τ₃ q) (homologyMap φ.τ₁ (q + 1))
    (HomologySequence.δ_naturality φ hS₁ hS₂ (q - 1) q hp)
    (by
      dsimp [R₁, R₂]
      rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₁₂])
    (by
      dsimp [R₁, R₂]
      rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₂₃])
    (HomologySequence.δ_naturality φ hS₁ hS₂ q (q + 1) hn)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono he₁ he₂ ψ
    (by dsimp [ψ]; infer_instance) (by dsimp [ψ]; infer_instance)
    (by dsimp [ψ]; infer_instance) (by dsimp [ψ]; infer_instance)

end SerrePositivity.DifferentialGraded
end

end ShortExactComparison

/-! ## ScalarHomShortExact（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomShortExact.lean） -/

/-! # 全次数で分裂するHom短完全列の実際の係数変更比較 -/

@[expose] public section ScalarHomShortExact
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

namespace ModuleGradedSplit
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- Homの次数ごとのsectionを線形射として保持する。chain map条件は課さない。 -/
def homRestrictionSectionLinear (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) T)).X q ⟶
      (moduleHom A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).X q :=
  ModuleCat.ofHom {
    toFun := s.homRestrictionSection T q
    map_add' a b := by simp only [homRestrictionSection, forward, TensorProduct.tmul_add, map_add]
    map_smul' c a := by
      simp only [homRestrictionSection, forward, TensorProduct.tmul_smul, map_smul]
      rfl }

def homShortComplexDegreewiseSplitting (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ) :
    ((s.homShortComplex T).map (HomologicalComplex.eval (ModuleCat A) (.up ℤ) q)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (s.homShortComplex_degreewise_shortExact T q).exact
    (s.homRestrictionSectionLinear D T q) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact s.homRestriction_section T q z)
    (s.homShortComplex_degreewise_shortExact T q).mono_f

lemma scalarHomShortComplex_shortExact (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) :
    ((s.homShortComplex T).map (ScalarExtension.extension φ)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q =>
    ((s.homShortComplexDegreewiseSplitting D T q).map (ModuleCat.extendScalars φ)).shortExact)

end ModuleGradedSplit

def scalarModuleHomShortComplex {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    (s.homShortComplex T).map (ScalarExtension.extension φ) ⟶
      (scalarModuleGradedSplit φ D s).homShortComplex
        ((ScalarExtension.moduleExtension φ D).obj T) where
  τ₁ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) T)
  τ₂ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)
  τ₃ := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) T)
  comm₁₂ := (scalarModuleHom_precompose φ D g T).symm
  comm₂₃ := (scalarModuleHom_precompose φ D f T).symm

lemma scalarModuleHom_gradedSplit_middle {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (hP : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)))
    (hM : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)) :=
  complexQuasiIso_middle_of_shortExact (scalarModuleHomShortComplex φ D s T)
    (s.scalarHomShortComplex_shortExact φ D T)
    ((scalarModuleGradedSplit φ D s).homShortComplex_shortExact
      ((ScalarExtension.moduleExtension φ D).obj T)) hP hM

end SerrePositivity.DifferentialGraded
end

end ScalarHomShortExact

/-! ## EnhancementComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementComparison.lean） -/

/-! # U13の指定enhancementと全加群内のEndの照合 -/

@[expose] public section EnhancementComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

/-- U13のenhancement内のEndを、実際の右加群の全Endへ送る。 -/
def perfectEndomorphismUnderlying :
    DGFunctor A (EndomorphismObject E) (EndomorphismObject E.val) :=
  endomorphismMap A (perfectDGModuleInclusion A D S) E

/-- U13は充満dg部分圏なので、比較は全Hom複体上の恒等写像。 -/
lemma perfectEndomorphismUnderlying_map (x y : EndomorphismObject E) :
    (perfectEndomorphismUnderlying A D S E).map x y = 𝟙 _ := rfl

lemma perfectEndomorphismUnderlying_homQuasiIso :
    HomQuasiIso (perfectEndomorphismUnderlying A D S E) := by
  intro x y
  rw [perfectEndomorphismUnderlying_map]
  infer_instance

/-- H⁰の本質的全射性はHomの擬同型とは別の証拠として保持する。 -/
lemma perfectEndomorphismUnderlying_essSurj :
    (perfectEndomorphismUnderlying A D S E).onHomotopy.EssSurj where
  mem_essImage X := by
    refine ⟨(toHomotopy A (EndomorphismObject E)).obj
      (ForgetEnrichment.of (Complex A) .point), ⟨?_⟩⟩
    obtain ⟨X⟩ := X
    obtain ⟨X⟩ := X
    exact Iso.refl _

/-- 二つのEndの比較は準同値。thick生成の仮定は不要。 -/
lemma perfectEndomorphismUnderlying_quasiEquivalence :
    QuasiEquivalence (perfectEndomorphismUnderlying A D S E) :=
  ⟨perfectEndomorphismUnderlying_homQuasiIso A D S E,
    perfectEndomorphismUnderlying_essSurj A D S E⟩

/-- 指定enhancementから、実際のEのEndに値を持つHom関手。 -/
def perfectEndomorphismModuleHom :
    DGFunctor A (PerfectDGModuleOver A D S) (RightModule A (EndomorphismObject E.val)) :=
  (perfectDGModuleInclusion A D S).comp (endomorphismModuleHom A D E.val)

/-- enhancement内のHom(E,M)は、Endの比較に沿った実際の加群Homの制限と一致する。 -/
lemma perfectEndomorphismHomRight_comparison (M : PerfectDGModuleOver A D S) :
    endomorphismHomRight A (PerfectDGModuleOver A D S) E M =
      restrictModule A (EndomorphismObject E) (EndomorphismObject E.val)
        (perfectEndomorphismUnderlying A D S E).op
        ((perfectEndomorphismModuleHom A D S E).obj M) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- U13の指定対象に対する再構成導来随伴。射影性は対象の証拠から取る。 -/
def perfectEndomorphismDerivedAdjunction :
    endomorphismDerivedTensor A D E.val ⊣ endomorphismDerivedHom A D E.val E.property.1 :=
  endomorphismDerivedAdjunction A D E.val E.property.1

end SerrePositivity.DifferentialGraded
end

end EnhancementComparison

/-! ## GeneratorHomIso（旧 SerrePositivity/DifferentialGraded/Endomorphism/GeneratorHomIso.lean） -/

/-! # 指定対象を始域とする再構成Hom写像とdg Yoneda -/

@[expose] public section GeneratorHomIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 正則End加群とHom(E,E)の閉零同型。 -/
def endomorphismRegularModuleIso :
    ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))) ≅
      ForgetEnrichment.of (Complex A) ((endomorphismModuleHom A D E).obj E) :=
  (eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (endomorphismModuleHom_self A D E))).symm

lemma endomorphismRegularModuleIso_hom_eval (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map
      (endomorphismRegularModuleIso A D E).hom = 𝟙 _ := by
  change (moduleEvaluation A (EndomorphismObject E) b).map
    (eqToHom (congrArg (ForgetEnrichment.of (Complex A))
      (endomorphismModuleHom_self A D E)).symm) = _
  rw [eqToHom_map]
  rfl

lemma endomorphismGeneratorYonedaApp (M : RightModule A D) (b : EndomorphismObject E) :
    yonedaExtensionApp A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M) (𝟙 _) (op b) =
      (leftRepresentable A E).map E M := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [yonedaExtensionApp_apply]
  change (p * r).negOnePow • forward A (D := RightModule A D) m f hn = _
  exact (leftRepresentable_action A E E M f m hn).symm

lemma endomorphismModuleHom_generator_map_yoneda (M : RightModule A D) :
    (endomorphismModuleHom A D E).map E M ≫
        moduleHomPrecompose A (EndomorphismObject E)
          (representable A (EndomorphismObject.point (E := E)))
          ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M)
          (endomorphismRegularModuleIso A D E).hom =
      (dgYonedaIso A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M)).inv := by
  apply moduleHom_ext
  intro b
  rw [Category.assoc, moduleHomPrecompose_π]
  change (endomorphismModuleHom A D E).map E M ≫
    moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
      ((endomorphismModuleHom A D E).obj M) b ≫
      homPrecompose ((moduleEvaluation A (EndomorphismObject E) b).map
        (endomorphismRegularModuleIso A D E).hom) (moduleHom A D E M) = _
  rw [endomorphismRegularModuleIso_hom_eval]
  have hid : homPrecompose (𝟙 (moduleHom A D E E)) (moduleHom A D E M) = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Cochain.id_comp z
  change (endomorphismModuleHom A D E).map E M ≫
    moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
      ((endomorphismModuleHom A D E).obj M) b ≫
      homPrecompose (𝟙 (moduleHom A D E E)) (moduleHom A D E M) = _
  rw [hid]
  have hcalc : (endomorphismModuleHom A D E).map E M ≫
      moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj E)
        ((endomorphismModuleHom A D E).obj M) b =
      (dgYonedaIso A (EndomorphismObject.point (E := E))
        ((endomorphismModuleHom A D E).obj M)).inv ≫
        moduleHomπ A (EndomorphismObject E) (representable A .point)
          ((endomorphismModuleHom A D E).obj M) b := by
    cases b
    have hy := moduleHomEquiv_symm_π A (EndomorphismObject E) _
      (representable A .point) ((endomorphismModuleHom A D E).obj M)
      (yonedaExtension A .point ((endomorphismModuleHom A D E).obj M) (𝟙 _)) .point
    exact (endomorphismModuleHom_map_π A D E E M).trans
      ((endomorphismGeneratorYonedaApp A D E M .point).symm.trans hy.symm)
  exact (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hcalc)

/-- 始域Eからの全Hom写像はchain iso。Eの射影性・compact性は不要。 -/
lemma endomorphismModuleHom_generator_isIso (M : RightModule A D) :
    IsIso ((endomorphismModuleHom A D E).map E M) := by
  let i := endomorphismRegularModuleIso A D E
  let α := Iso.eHomCongr (Complex A) i.symm
    (Iso.refl (ForgetEnrichment.of (Complex A) ((endomorphismModuleHom A D E).obj M)))
  have hα : α.hom = moduleHomPrecompose A (EndomorphismObject E)
      (representable A (EndomorphismObject.point (E := E)))
      ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M) i.hom := by
    simp [α, Iso.eHomCongr, moduleHomPrecompose]
  have : IsIso (moduleHomPrecompose A (EndomorphismObject E)
      (representable A (EndomorphismObject.point (E := E)))
      ((endomorphismModuleHom A D E).obj E) ((endomorphismModuleHom A D E).obj M) i.hom) := by
    rw [← hα]
    infer_instance
  exact IsIso.of_isIso_fac_right (endomorphismModuleHom_generator_map_yoneda A D E M)

lemma endomorphismModuleHom_generator_quasiIso (M : RightModule A D) :
    QuasiIso ((endomorphismModuleHom A D E).map E M) := by
  have := endomorphismModuleHom_generator_isIso A D E M
  infer_instance

end SerrePositivity.DifferentialGraded
end

end GeneratorHomIso

/-! ## HomMapNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomMapNaturality.lean） -/

/-! # dg関手の全Hom写像と閉零前後合成の可換性 -/

@[expose] public section HomMapNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {C : Type v} {B : Type w}
  [DGCategory A C] [DGCategory A B] (F : DGFunctor A C B)

lemma dgHomMap_precompose {X X' : ClosedCategory A C} (f : X ⟶ X')
    (Y : ClosedCategory A C) :
    eHomWhiskerRight (Complex A) f Y ≫ F.map X Y =
      F.map X' Y ≫ eHomWhiskerRight (Complex A) (F.onClosed.map f) (F.onClosed.obj Y) := by
  dsimp only [eHomWhiskerRight]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerRight_comp_tensorHom_assoc,
    leftUnitor_inv_comp_tensorHom_assoc]
  rfl

lemma dgHomMap_postcompose (X : ClosedCategory A C) {Y Y' : ClosedCategory A C}
    (g : Y ⟶ Y') :
    eHomWhiskerLeft (Complex A) X g ≫ F.map X Y' =
      F.map X Y ≫ eHomWhiskerLeft (Complex A) (F.onClosed.obj X) (F.onClosed.map g) := by
  dsimp only [eHomWhiskerLeft]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerLeft_comp_tensorHom_assoc,
    rightUnitor_inv_comp_tensorHom_assoc]
  rfl

end SerrePositivity.DifferentialGraded
end

end HomMapNaturality

/-! ## HomComparisonRetracts（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomComparisonRetracts.lean） -/

/-! # 再構成Homの擬同型条件はK内の始域retractに安定 -/

@[expose] public section HomComparisonRetracts
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismHomComparison_of_homotopyRetract
    {P Q : ModuleCategory A D} (i : P ⟶ Q) (r : Q ⟶ P)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 P))
    (T : ModuleCategory A D)
    (hQ : QuasiIso ((endomorphismModuleHom A D E).map Q T)) :
    QuasiIso ((endomorphismModuleHom A D E).map P T) := by
  let F := endomorphismModuleHom A D E
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D (i ≫ r) (𝟙 P)).mp h
  have hF : (moduleToHomotopy A (EndomorphismObject E)).map (F.onClosed.map (i ≫ r)) =
      (moduleToHomotopy A (EndomorphismObject E)).map (F.onClosed.map (𝟙 P)) :=
    congrArg F.onHomotopy.map h
  obtain ⟨ht⟩ := (moduleToHomotopy_map_eq_iff A (EndomorphismObject E) _ _).mp hF
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hs := (moduleHomPrecomposeHomotopy A D hh T).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id, homologyMap_comp, homologyMap_id] at hs
  have ht' := (moduleHomPrecomposeHomotopy A (EndomorphismObject E) ht
    (F.onClosed.obj T)).homologyMap_eq q
  simp only [Functor.map_comp, eHomWhiskerRight_comp, homologyMap_comp] at ht'
  have htId := congrArg (fun k => homologyMap
    (eHomWhiskerRight (Complex A) k (F.onClosed.obj T)) q) (F.onClosed.map_id P)
  simp only [eHomWhiskerRight_id, homologyMap_id] at htId
  have htFinal := ht'.trans htId
  let a : RetractArrow (homologyMap (F.map P T) q) (homologyMap (F.map Q T) q) :=
    { i := Arrow.homMk
        (homologyMap (eHomWhiskerRight (Complex A) r T) q)
        (homologyMap (eHomWhiskerRight (Complex A) (F.onClosed.map r) (F.onClosed.obj T)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (dgHomMap_precompose F r T)
          simp only [homologyMap_comp] at hn
          exact hn)
      r := Arrow.homMk
        (homologyMap (eHomWhiskerRight (Complex A) i T) q)
        (homologyMap (eHomWhiskerRight (Complex A) (F.onClosed.map i) (F.onClosed.obj T)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (dgHomMap_precompose F i T)
          simp only [homologyMap_comp] at hn
          exact hn)
      retract := by
        apply Arrow.hom_ext
        · exact hs
        · exact htFinal }
  have : QuasiIso (F.map Q T) := hQ
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (ModuleCat A)) a
    (by infer_instance)

lemma endomorphismHomComparison_of_retract
    {P Q : ModuleCategory A D}
    (a : Retract ((moduleToHomotopy A D).obj P) ((moduleToHomotopy A D).obj Q))
    (T : ModuleCategory A D)
    (hQ : QuasiIso ((endomorphismModuleHom A D E).map Q T)) :
    QuasiIso ((endomorphismModuleHom A D E).map P T) := by
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
  obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
  apply endomorphismHomComparison_of_homotopyRetract A D E i r _ T hQ
  rw [CategoryTheory.Functor.map_comp, hi, hr, a.retract]
  exact ((moduleToHomotopy A D).map_id P).symm

/-- 全ての終域に対し再構成Hom写像が擬同型になる、K(D)内の始域の性質。 -/
def endomorphismHomComparisonLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => ∀ T : ModuleCategory A D, QuasiIso ((endomorphismModuleHom A D E).map X.as T)

instance endomorphismHomComparisonLocusStableUnderRetracts :
    (endomorphismHomComparisonLocus A D E).IsStableUnderRetracts where
  of_retract a hQ T := endomorphismHomComparison_of_retract A D E a T (hQ T)

lemma endomorphismHomComparisonLocus_generator :
    endomorphismHomComparisonLocus A D E
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E)) := by
  intro T
  exact endomorphismModuleHom_generator_quasiIso A D E T

end SerrePositivity.DifferentialGraded
end

end HomComparisonRetracts

/-! ## HomComparisonShift（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomComparisonShift.lean） -/

/-! # 全次数Hom比較と反変shiftの可換図式 -/

@[expose] public section HomComparisonShift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex

lemma complexShiftIsoOfSumZero_hom {A : Type u} [CommRing A]
    {K L : Complex A} {s t : ℤ} (α : Cochain K L s) (hα : δ s (s + 1) α = 0)
    (β : Cochain L K t) (hst : s + t = 0)
    (hαβ : α.comp β hst = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (by omega : t + s = 0) = Cochain.ofHom (𝟙 L)) :
    (complexShiftIsoOfSumZero A α hα β hst hαβ hβα).hom = complexShiftComparison A α hα := by
  have ht : t = -s := by omega
  subst t
  rfl

lemma dgHomMap_contra_naturality {A : Type u} [CommRing A]
    {C : Type v} {B : Type w} [DGCategory A C] [DGCategory A B]
    (F : DGFunctor A C B) (T : C) (x y : Cᵒᵖ) :
    (representable A T).map x y ≫
        homPostcompose ((representable A T).obj x) (F.map y.unop T) =
      (F.op.comp (representable A (F.obj T))).map x y ≫
        homPrecompose (F.map x.unop T) ((F.op.comp (representable A (F.obj T))).obj y) := by
  apply closedFamily_of_action A
    (M := representable A T) (N := F.op.comp (representable A (F.obj T)))
    (fun z => F.map z.unop T)
  intro x y p r n hn f v
  exact F.map_forward A f v (by omega)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma contraShiftComparison_naturality
    (F G : DGFunctor A (RightModule A D)ᵒᵖ (Complex A))
    (a : ∀ x : (RightModule A D)ᵒᵖ, F.obj x ⟶ G.obj x)
    (h : ∀ x y, F.map x y ≫ homPostcompose (F.obj x) (a y) =
      G.map x y ≫ homPrecompose (a x) (G.obj y))
    (s : ℤ) (M : RightModule A D) :
    a (op (shiftModule s M)) ≫ (DGFunctor.moduleShiftOppImageIso A D G s M).hom =
      (DGFunctor.moduleShiftOppImageIso A D F s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map (a (op M)) := by
  change a _ ≫ (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom =
    (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom ≫ _
  rw [complexShiftIsoOfSumZero_hom, complexShiftIsoOfSumZero_hom]
  apply HomologicalComplex.hom_ext
  intro i
  rw [comp_f, comp_f, complexShiftComparison_f, complexShiftComparison_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (closedFamily_action A a h (op (shiftModule s M)) (op M) (-s) i (i + -s)
    rfl (moduleShiftInElement A D s M) v).symm

variable (E : RightModule A D)

/-- 指定Hom比較の始域の整数shiftに対する全次数可換図式。 -/
lemma endomorphismHomComparison_shift_square (s : ℤ) (M T : RightModule A D) :
    (endomorphismModuleHom A D E).map (shiftModule s M) T ≫
        (DGFunctor.moduleShiftOppImageIso A D
          ((endomorphismModuleHom A D E).op.comp
            (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom =
      (DGFunctor.moduleShiftOppImageIso A D (representable A T) s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map
          ((endomorphismModuleHom A D E).map M T) :=
  contraShiftComparison_naturality A D (representable A T)
    ((endomorphismModuleHom A D E).op.comp
      (representable A ((endomorphismModuleHom A D E).obj T)))
    (fun x => (endomorphismModuleHom A D E).map x.unop T)
    (dgHomMap_contra_naturality (endomorphismModuleHom A D E) T) s M

lemma endomorphismHomComparison_shift (s : ℤ) (M T : RightModule A D)
    (hM : QuasiIso ((endomorphismModuleHom A D E).map M T)) :
    QuasiIso ((endomorphismModuleHom A D E).map (shiftModule s M) T) := by
  have := hM
  have h := endomorphismHomComparison_shift_square A D E s M T
  have hs : QuasiIso ((endomorphismModuleHom A D E).map (shiftModule s M) T ≫
      (DGFunctor.moduleShiftOppImageIso A D
        ((endomorphismModuleHom A D E).op.comp
          (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right ((endomorphismModuleHom A D E).map (shiftModule s M) T)
    (DGFunctor.moduleShiftOppImageIso A D
      ((endomorphismModuleHom A D E).op.comp
        (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom

instance endomorphismHomComparisonLocusStableUnderShift :
    (endomorphismHomComparisonLocus A D E).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    intro X hX
    apply (endomorphismHomComparisonLocus A D E).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
    intro T
    exact endomorphismHomComparison_shift A D E s X.as T (hX T)⟩

end SerrePositivity.DifferentialGraded
end

end HomComparisonShift

/-! ## HomComparisonCone（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomComparisonCone.lean） -/

/-! # 全次数分裂のHom短完全列による再構成Hom比較のcone閉性 -/

@[expose] public section HomComparisonCone
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- 全Hom写像を、全次数分裂のHom短完全列の間の射として保持する。 -/
def dgHomMapShortComplex {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    s.homShortComplex T ⟶
      (dgModuleFunctorGradedSplit A D B F s).homShortComplex (F.onClosed.obj T) where
  τ₁ := F.map P T
  τ₂ := F.map N T
  τ₃ := F.map M T
  comm₁₂ := (dgHomMap_precompose F g T).symm
  comm₂₃ := (dgHomMap_precompose F f T).symm

lemma dgHomMap_gradedSplit_middle {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (hP : QuasiIso (F.map P T)) (hM : QuasiIso (F.map M T)) : QuasiIso (F.map N T) :=
  complexQuasiIso_middle_of_shortExact (dgHomMapShortComplex A D B F s T)
    (s.homShortComplex_shortExact T)
    ((dgModuleFunctorGradedSplit A D B F s).homShortComplex_shortExact (F.onClosed.obj T)) hP hM

variable (E : RightModule A D)

lemma endomorphismHomComparison_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D)
    (hM : QuasiIso ((endomorphismModuleHom A D E).map M T))
    (hN : QuasiIso ((endomorphismModuleHom A D E).map N T)) :
    QuasiIso ((endomorphismModuleHom A D E).map (moduleCone A D f) T) :=
  dgHomMap_gradedSplit_middle A D (EndomorphismObject E) (endomorphismModuleHom A D E)
    (moduleConeGradedSplit A D f) T
    (endomorphismHomComparison_shift A D E 1 M T hM) hN

lemma endomorphismHomComparisonLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (ModuleHomotopyCategory A D))
    (h₁ : endomorphismHomComparisonLocus A D E T.obj₁)
    (h₂ : endomorphismHomComparisonLocus A D E T.obj₂) :
    endomorphismHomComparisonLocus A D E T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₂.mapIso e) h₂
  apply (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₃.mapIso e.symm)
  intro Q
  exact endomorphismHomComparison_cone A D E f Q (hM Q) (hN Q)

instance endomorphismHomComparisonLocusTriangulatedClosed₃ :
    (endomorphismHomComparisonLocus A D E).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (endomorphismHomComparisonLocus_triangle_obj₃ A D E)

instance endomorphismHomComparisonLocusTriangulatedClosed₂ :
    (endomorphismHomComparisonLocus A D E).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance endomorphismHomComparisonLocusNonempty :
    (endomorphismHomComparisonLocus A D E).Nonempty :=
  ObjectProperty.nonempty_of_prop (endomorphismHomComparisonLocus_generator A D E)

instance endomorphismHomComparisonLocusContainsZero :
    (endomorphismHomComparisonLocus A D E).ContainsZero := inferInstance

instance endomorphismHomComparisonLocusIsTriangulated :
    (endomorphismHomComparisonLocus A D E).IsTriangulated where

end SerrePositivity.DifferentialGraded
end

end HomComparisonCone
