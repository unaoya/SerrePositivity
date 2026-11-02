module

public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-!
# Functor.ModuleShift

## 概要
5 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ModuleShift（旧 SerrePositivity/DifferentialGraded/Functor/ModuleShift.lean） -/

/-! # 複体値dg関手の加群shift比較 -/

@[expose] public section ModuleShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (Complex A))

def moduleShiftImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (shiftModule s M)) (F.obj M) s :=
  (F.map (shiftModule s M) M).f s (moduleShiftOutElement A D s M)

def moduleShiftImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj M) (F.obj (shiftModule s M)) (-s) :=
  (F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M)

lemma moduleShiftImageOut_d (s : ℤ) (M : RightModule A D) :
    δ s (s + 1) (moduleShiftImageOut A D F s M) = 0 := by
  have h := F.map_d_cochain A (moduleShiftOutElement A D s M) (q := s + 1)
  have hz : (F.map (shiftModule s M) M).f (s + 1)
      ((moduleHom A D (shiftModule s M) M).d s (s + 1)
        (moduleShiftOutElement A D s M)) = 0 := by
    rw [moduleShiftOutElement_d, map_zero]
  exact h.symm.trans hz

lemma moduleShiftImageOutIn (s : ℤ) (M : RightModule A D) :
    (moduleShiftImageOut A D F s M).comp (moduleShiftImageIn A D F s M)
        (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (shiftModule s M))) := by
  have h := congrArg (fun z => (F.map (shiftModule s M) (shiftModule s M)).f 0 z)
    (moduleShiftOutIn A D s M)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleShiftImageInOut (s : ℤ) (M : RightModule A D) :
    (moduleShiftImageIn A D F s M).comp (moduleShiftImageOut A D F s M)
        (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj M)) := by
  have h := congrArg (fun z => (F.map M M).f 0 z) (moduleShiftInOut A D s M)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

/-- 全次数Hom写像によって得る、F(M[s])からF(M)[s]への実際のchain map。 -/
def moduleShiftImageComparison (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ⟶ (F.obj M)⟦s⟧ :=
  Cocycle.equivHomShift.symm
    (Cocycle.mk (moduleShiftImageOut A D F s M) (s + 1) rfl (moduleShiftImageOut_d A D F s M))

lemma moduleShiftImageComparison_f (s : ℤ) (M : RightModule A D) (i : ℤ) :
    (moduleShiftImageComparison A D F s M).f i =
      (moduleShiftImageOut A D F s M).v i (i + s) rfl := by
  simp only [moduleShiftImageComparison, Cocycle.equivHomShift_symm_apply,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.mk_coe]
  rw [Cochain.rightShift_v _ s 0 (zero_add s) i i (add_zero i) (i + s) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

/-- 比較射の各次数の逆は、次数−sの包含の像で与えられる。 -/
lemma moduleShiftImageComparison_bijective (s : ℤ) (M : RightModule A D) (i : ℤ) :
    Function.Bijective ((moduleShiftImageComparison A D F s M).f i) := by
  let ψ : (F.obj M).X (i + s) → (F.obj (shiftModule s M)).X i :=
    (moduleShiftImageIn A D F s M).v (i + s) i (by omega)
  have hl : Function.LeftInverse ψ ((moduleShiftImageComparison A D F s M).f i) := by
    intro z
    have h := Cochain.congr_v (moduleShiftImageOutIn A D F s M) i i (add_zero i)
    rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [moduleShiftImageComparison_f]
    exact hz
  have hr : Function.RightInverse ψ ((moduleShiftImageComparison A D F s M).f i) := by
    intro z
    have h := Cochain.congr_v (moduleShiftImageInOut A D F s M) (i + s) (i + s)
      (add_zero (i + s))
    rw [Cochain.comp_v _ _ _ (i + s) i (i + s) (by omega) rfl, Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [moduleShiftImageComparison_f]
    exact hz
  exact ⟨hl.injective, hr.surjective⟩

instance moduleShiftImageComparison_isIso (s : ℤ) (M : RightModule A D) :
    IsIso (moduleShiftImageComparison A D F s M) := by
  have (i : ℤ) : IsIso ((moduleShiftImageComparison A D F s M).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (moduleShiftImageComparison_bijective A D F s M i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 任意複体値dg関手の、整数shiftに対する具体的比較同型。 -/
def moduleShiftImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ≅ (F.obj M)⟦s⟧ :=
  asIso (moduleShiftImageComparison A D F s M)

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleShift

/-! ## ModuleShiftOpposite（旧 SerrePositivity/DifferentialGraded/Functor/ModuleShiftOpposite.lean） -/

/-! # 反変複体値dg関手による加群shiftの比較 -/

@[expose] public section ModuleShiftOpposite
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D)ᵒᵖ (Complex A))

def moduleShiftOppImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (Opposite.op (shiftModule s M))) (F.obj (Opposite.op M)) (-s) :=
  (F.map (Opposite.op (shiftModule s M)) (Opposite.op M)).f (-s) (moduleShiftInElement A D s M)

def moduleShiftOppImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (Opposite.op M)) (F.obj (Opposite.op (shiftModule s M))) s :=
  (s * s).negOnePow •
    (F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M)

lemma moduleShiftOppImageOut_d (s : ℤ) (M : RightModule A D) :
    δ (-s) (-s + 1) (moduleShiftOppImageOut A D F s M) = 0 := by
  have h := F.map_d_cochain A
    (x := Opposite.op (shiftModule s M)) (y := Opposite.op M) (moduleShiftInElement A D s M) (q := -s + 1)
  have hz : (F.map (Opposite.op (shiftModule s M)) (Opposite.op M)).f (-s + 1)
      ((moduleHom A D M (shiftModule s M)).d (-s) (-s + 1)
        (moduleShiftInElement A D s M)) = 0 := by
    rw [moduleShiftInElement_d, map_zero]
  exact h.symm.trans hz

lemma moduleShiftOppImageOutIn (s : ℤ) (M : RightModule A D) :
    (moduleShiftOppImageOut A D F s M).comp (moduleShiftOppImageIn A D F s M)
        (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj (Opposite.op (shiftModule s M)))) := by
  have hs := opposite_compose A (RightModule A D)
    (Opposite.op (shiftModule s M)) (Opposite.op M) (Opposite.op (shiftModule s M)) (-s) s 0 (neg_add_cancel s)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M)
  rw [moduleShiftOutIn] at hs
  simp only [neg_mul, Int.negOnePow_neg] at hs
  have h := congrArg (fun z => (F.map (Opposite.op (shiftModule s M))
    (Opposite.op (shiftModule s M))).f 0 z) hs
  rw [map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change (moduleShiftOppImageOut A D F s M).comp
      ((F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M))
        (neg_add_cancel s) =
    (s * s).negOnePow • (F.map (Opposite.op (shiftModule s M)) (Opposite.op (shiftModule s M))).f 0
      (unitElement A (Opposite.op (shiftModule s M))).val at h
  rw [map_unitElement, Bimodule.complex_unitElement] at h
  rw [moduleShiftOppImageIn, Cochain.comp_units_smul, h, smul_smul,
    Int.units_mul_self, one_smul]

lemma moduleShiftOppImageInOut (s : ℤ) (M : RightModule A D) :
    (moduleShiftOppImageIn A D F s M).comp (moduleShiftOppImageOut A D F s M)
        (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (Opposite.op M))) := by
  have hs := opposite_compose A (RightModule A D)
    (Opposite.op M) (Opposite.op (shiftModule s M)) (Opposite.op M) s (-s) 0 (add_neg_cancel s)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M)
  rw [moduleShiftInOut] at hs
  simp only [mul_neg, Int.negOnePow_neg] at hs
  have h := congrArg (fun z => (F.map (Opposite.op M) (Opposite.op M)).f 0 z) hs
  rw [map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change ((F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M)).comp
      (moduleShiftOppImageOut A D F s M) (add_neg_cancel s) =
    (s * s).negOnePow • (F.map (Opposite.op M) (Opposite.op M)).f 0 (unitElement A (Opposite.op M)).val at h
  rw [map_unitElement, Bimodule.complex_unitElement] at h
  rw [moduleShiftOppImageIn, Cochain.units_smul_comp, h, smul_smul,
    Int.units_mul_self, one_smul]

/-- 反変dg関手は加群のshiftを符号反転した通常shiftへ送る。 -/
def moduleShiftOppImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (Opposite.op (shiftModule s M)) ≅ (F.obj (Opposite.op M))⟦-s⟧ :=
  complexShiftIsoOfSumZero A (moduleShiftOppImageOut A D F s M)
    (moduleShiftOppImageOut_d A D F s M) (moduleShiftOppImageIn A D F s M)
    (neg_add_cancel s) (moduleShiftOppImageOutIn A D F s M) (moduleShiftOppImageInOut A D F s M)

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleShiftOpposite

/-! ## ModuleConeRelations（旧 SerrePositivity/DifferentialGraded/Functor/ModuleConeRelations.lean） -/

/-! # 複体値dg関手で送ったconeの行列恒等式 -/

@[expose] public section ModuleConeRelations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (Complex A)) {M N : ModuleCategory A D}

def moduleConeImageFst (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj (moduleCone A D f)) ((F.toComplexFunctor A).obj M) 1 :=
  (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) M)).f 1 (moduleConeFstElement A D f)

def moduleConeImageSnd (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj (moduleCone A D f)) ((F.toComplexFunctor A).obj N) 0 :=
  (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) N)).f 0 (moduleConeSndElement A D f)

lemma moduleConeImage_inl_fst (f : M ⟶ N) :
    (moduleConeImageInl A D F f).comp (moduleConeImageFst A D F f) (neg_add_cancel 1) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj M)) := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) M)).f 0 z) (moduleCone_inl_fst A D f)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleConeImage_inl_snd (f : M ⟶ N) :
    (moduleConeImageInl A D F f).comp (moduleConeImageSnd A D F f) (add_zero (-1)) = 0 := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).f (-1) z) (moduleCone_inl_snd A D f)
  rw [map_compose_cochain, map_zero] at h
  exact h

lemma moduleConeImage_inr_fst (f : M ⟶ N) :
    (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))).comp
      (moduleConeImageFst A D F f) (zero_add 1) = 0 := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M)).f 1 z) (moduleCone_inr_fst A D f)
  rw [map_compose_cochain, moduleConeInrElement, map_closedElement, map_zero] at h
  exact h

lemma moduleConeImage_inr_snd (f : M ⟶ N) :
    (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))).comp
      (moduleConeImageSnd A D F f) (zero_add 0) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj N)) := by
  have h := congrArg (fun z => (F.map (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) N)).f 0 z) (moduleCone_inr_snd A D f)
  rw [map_compose_cochain, moduleConeInrElement, map_closedElement,
    map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleConeImage_decomposition (f : M ⟶ N) :
    (moduleConeImageFst A D F f).comp (moduleConeImageInl A D F f) (add_neg_cancel 1) +
      (moduleConeImageSnd A D F f).comp
        (Cochain.ofHom ((F.toComplexFunctor A).map (moduleConeInr A D f))) (add_zero 0) =
      Cochain.ofHom (𝟙 ((F.toComplexFunctor A).obj (moduleCone A D f))) := by
  have h := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0 z)
    (moduleCone_decomposition A D f)
  rw [map_add, map_compose_cochain, map_compose_cochain, moduleConeInrElement,
    map_closedElement, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleConeRelations

/-! ## ModuleConeIso（旧 SerrePositivity/DifferentialGraded/Functor/ModuleConeIso.lean） -/

/-! # 複体値dg関手は主dg加群の標準coneを保つ -/

@[expose] public section ModuleConeIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleConeImageComparison_isIso (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) : IsIso (moduleConeImageComparison A D F f) :=
  complexConeDesc_isIso A ((F.toComplexFunctor A).map f)
    (moduleConeImageInl A D F f) ((F.toComplexFunctor A).map (moduleConeInr A D f))
    (moduleConeImageFst A D F f) (moduleConeImageSnd A D F f) (moduleConeImageInl_d A D F f)
    (moduleConeImage_inl_fst A D F f) (moduleConeImage_inl_snd A D F f)
    (moduleConeImage_inr_fst A D F f) (moduleConeImage_inr_snd A D F f)
    (moduleConeImage_decomposition A D F f)

/-- 非有界coneの実際の複体同型。 -/
def moduleConeImageIso (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((F.toComplexFunctor A).map f) ≅ (F.toComplexFunctor A).obj (moduleCone A D f) :=
  asIso (moduleConeImageComparison A D F f)

lemma moduleConeImageIso_hom (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleConeImageIso A D F f).hom = moduleConeImageComparison A D F f := rfl

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ModuleConeIso

/-! ## QuasiEquivalenceTensor（旧 SerrePositivity/DifferentialGraded/Functor/QuasiEquivalenceTensor.lean） -/

/-! # 局所K-flat性を明示したtensor積dg関手の準同値保存

## 概要
局所K-flat性を明示したtensor積dg関手の準同値保存。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section QuasiEquivalenceTensor
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w} {D : Type z} {E : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

/-- まずF、次にGのHom写像をtensorする。相手のK-flat性はCとDに要求する。 -/
lemma homQuasiIso_tensor (hF : HomQuasiIso F) (hG : HomQuasiIso G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) : HomQuasiIso (F.tensor G) := by
  intro x y
  have := hF x.1 y.1
  have := hG x.2 y.2
  have h₁ := complexKFlat_quasiIso_left A (hC x.2 y.2) (F.map x.1 y.1)
  have h₂ := complexKFlat_quasiIso_right A (hD (F.obj x.1) (F.obj y.1)) (G.map x.2 y.2)
  let := h₁
  let := h₂
  change QuasiIso (F.map x.1 y.1 ⊗ₘ G.map x.2 y.2)
  have hi : QuasiIso ((F.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)) ≫
      (𝟙 (F.obj x.1 ⟶[Complex A] F.obj y.1) ⊗ₘ G.map x.2 y.2)) := by infer_instance
  simpa only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp] using hi

/-- 本質的全射性のtensor保存自体にはflatnessを使わない。 -/
lemma DGFunctor.onHomotopy_tensor_essSurj (hF : F.onHomotopy.EssSurj)
    (hG : G.onHomotopy.EssSurj) : (F.tensor G).onHomotopy.EssSurj where
  mem_essImage y := by
    let := hF
    let := hG
    let e := ForgetEnrichment.to (Complex A) y.as
    let Y₁ := (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) e.1)
    let Y₂ := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e.2)
    let X₁ := F.onHomotopy.objPreimage Y₁
    let X₂ := G.onHomotopy.objPreimage Y₂
    let b := ForgetEnrichment.to (Complex A) X₁.as
    let c := ForgetEnrichment.to (Complex A) X₂.as
    let i₁ := F.onHomotopy.objObjPreimageIso Y₁
    let i₂ := G.onHomotopy.objObjPreimageIso Y₂
    refine ⟨(toHomotopy A (DGTensorCategory A B C)).obj
      (ForgetEnrichment.of (Complex A) ((b, c) : DGTensorCategory A B C)), ⟨?_⟩⟩
    exact ((dgTensorIncludeFirst A D E (G.obj c)).onHomotopy.mapIso i₁) ≪≫
      ((dgTensorIncludeSecond A D E e.1).onHomotopy.mapIso i₂)

lemma quasiEquivalence_tensor (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) : QuasiEquivalence (F.tensor G) :=
  ⟨homQuasiIso_tensor F G hF.1 hG.1 hC hD, F.onHomotopy_tensor_essSurj G hF.2 hG.2⟩

end SerrePositivity.DifferentialGraded
end

end QuasiEquivalenceTensor
