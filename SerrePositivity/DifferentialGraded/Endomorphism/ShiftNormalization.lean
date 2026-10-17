module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleShiftImage
public import SerrePositivity.DifferentialGraded.Module.ConeShiftSquares

/-! # 整合的shift比較のための斉次射影の符号正規化

MathlibのleftShiftに含まれる定数符号を明示的に除く。
既存の比較同型を変更せず、正規化した比較を別に構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
