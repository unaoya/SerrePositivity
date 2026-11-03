module

public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-!
# Endomorphism.Scalar.PerfectStability

## 概要
Hom 比較の shift・cone 閉性と perfect・射影的加群の保存をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarHomShift（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomShift.lean） -/

/-! # 係数変更した全次数Homの反変shift表示 -/

@[expose] public section ScalarHomShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarBaseChange_compose {D : Type v} [DGCategory A D]
    {x y z : D} {p q n : ℤ} (g : GradedHom A y z q) (f : GradedHom A x y p)
    (h : p + q = n) :
    let := φ.toAlgebra
    compose A' (D := ScalarExtension.DGBaseChange φ D)
      (x := x) (y := y) (z := z) ((1 : A') ⊗ₜ[A] g) ((1 : A') ⊗ₜ[A] f) h =
      (1 : A') ⊗ₜ[A] compose A g f h := by
  let := φ.toAlgebra
  unfold compose
  rw [scalarBaseChange_forward]
  simp only [Units.smul_def]
  exact (map_zsmul (TensorProduct.mk A A' _ (1 : A'))
    ((p * q).negOnePow : ℤ) (forward A f g h)).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ (Complex A'))

def scalarModuleShiftOppImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (op (shiftModule s M))) (F.obj (op M)) (-s) :=
  let := φ.toAlgebra
  (F.map (op (shiftModule s M)) (op M)).f (-s)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)

def scalarModuleShiftOppImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (op M)) (F.obj (op (shiftModule s M))) s :=
  let := φ.toAlgebra
  (s * s).negOnePow • (F.map (op M) (op (shiftModule s M))).f s
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)

lemma scalarModuleShiftOppImageOut_d (s : ℤ) (M : RightModule A D) :
    δ (-s) (-s + 1) (scalarModuleShiftOppImageOut φ D F s M) = 0 := by
  let := φ.toAlgebra
  have h := F.map_d_cochain A'
    (x := op (shiftModule s M)) (y := op M)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M) (q := -s + 1)
  have hz : (F.map (op (shiftModule s M)) (op M)).f (-s + 1)
      ((homObject A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ
        (op (shiftModule s M)) (op M)).d (-s) (-s + 1)
        ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)) = 0 := by
    change (F.map (op (shiftModule s M)) (op M)).f (-s + 1)
      ((ModuleCat.extendScalars φ).map ((moduleHom A D M (shiftModule s M)).d (-s) (-s + 1))
        ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)) = 0
    erw [ModuleCat.ExtendScalars.map_tmul φ]
    rw [moduleShiftInElement_d, TensorProduct.tmul_zero, map_zero]
  exact h.symm.trans hz

lemma scalarModuleShiftOppImageOutIn (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftOppImageOut φ D F s M).comp (scalarModuleShiftOppImageIn φ D F s M)
      (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj (op (shiftModule s M)))) := by
  let := φ.toAlgebra
  have hs := opposite_compose A' (ScalarExtension.DGBaseChange φ (RightModule A D))
    (op (shiftModule s M)) (op M) (op (shiftModule s M)) (-s) s 0 (neg_add_cancel s)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := shiftModule s M) (y := M) (z := shiftModule s M)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M) (add_neg_cancel s)
  have he := congrArg (fun z : GradedHom A (shiftModule s M) (shiftModule s M) 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftOutIn A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) (shiftModule s M)
  have hc' := hc.trans (he.trans hu.symm)
  have hs' := hs.trans (congrArg (fun z => (-s * s).negOnePow • z) hc')
  simp only [neg_mul, Int.negOnePow_neg] at hs'
  have h := congrArg (fun z => (F.map (op (shiftModule s M))
    (op (shiftModule s M))).f 0 z) hs'
  rw [DGFunctor.map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change (scalarModuleShiftOppImageOut φ D F s M).comp
      ((F.map (op M) (op (shiftModule s M))).f s
        ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)) (neg_add_cancel s) =
      (s * s).negOnePow • (F.map (op (shiftModule s M)) (op (shiftModule s M))).f 0
        (unitElement A' (op
          (show ScalarExtension.DGBaseChange φ (RightModule A D) from shiftModule s M))).val at h
  rw [F.map_unitElement A', Bimodule.complex_unitElement] at h
  rw [scalarModuleShiftOppImageIn, Cochain.comp_units_smul, h, smul_smul,
    Int.units_mul_self, one_smul]

lemma scalarModuleShiftOppImageInOut (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftOppImageIn φ D F s M).comp (scalarModuleShiftOppImageOut φ D F s M)
      (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (op M))) := by
  let := φ.toAlgebra
  have hs := opposite_compose A' (ScalarExtension.DGBaseChange φ (RightModule A D))
    (op M) (op (shiftModule s M)) (op M) s (-s) 0 (add_neg_cancel s)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := M) (y := shiftModule s M) (z := M)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M) (neg_add_cancel s)
  have he := congrArg (fun z : GradedHom A M M 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftInOut A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) M
  have hc' := hc.trans (he.trans hu.symm)
  have hs' := hs.trans (congrArg (fun z => (s * -s).negOnePow • z) hc')
  simp only [mul_neg, Int.negOnePow_neg] at hs'
  have h := congrArg (fun z => (F.map (op M) (op M)).f 0 z) hs'
  rw [DGFunctor.map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change ((F.map (op M) (op (shiftModule s M))).f s
      ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)).comp
      (scalarModuleShiftOppImageOut φ D F s M) (add_neg_cancel s) =
      (s * s).negOnePow • (F.map (op M) (op M)).f 0
        (unitElement A' (op
          (show ScalarExtension.DGBaseChange φ (RightModule A D) from M))).val at h
  rw [F.map_unitElement A', Bimodule.complex_unitElement] at h
  rw [scalarModuleShiftOppImageIn, Cochain.units_smul_comp, h, smul_smul,
    Int.units_mul_self, one_smul]

def scalarModuleShiftOppImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (op (shiftModule s M)) ≅ (F.obj (op M))⟦-s⟧ :=
  complexShiftIsoOfSumZero A' (scalarModuleShiftOppImageOut φ D F s M)
    (scalarModuleShiftOppImageOut_d φ D F s M) (scalarModuleShiftOppImageIn φ D F s M)
    (neg_add_cancel s) (scalarModuleShiftOppImageOutIn φ D F s M)
    (scalarModuleShiftOppImageInOut φ D F s M)

lemma scalarContraShiftComparison_naturality
    (G : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ (Complex A'))
    (a : ∀ x, F.obj x ⟶ G.obj x)
    (h : ∀ x y, F.map x y ≫ homPostcompose (F.obj x) (a y) =
      G.map x y ≫ homPrecompose (a x) (G.obj y))
    (s : ℤ) (M : RightModule A D) :
    a (op (shiftModule s M)) ≫ (scalarModuleShiftOppImageIso φ D G s M).hom =
      (scalarModuleShiftOppImageIso φ D F s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A') (-s)).map (a (op M)) := by
  let := φ.toAlgebra
  change a _ ≫ (complexShiftIsoOfSumZero A' _ _ _ _ _ _).hom =
    (complexShiftIsoOfSumZero A' _ _ _ _ _ _).hom ≫ _
  rw [complexShiftIsoOfSumZero_hom, complexShiftIsoOfSumZero_hom]
  apply HomologicalComplex.hom_ext
  intro i
  rw [comp_f, comp_f, complexShiftComparison_f, complexShiftComparison_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (closedFamily_action A' a h (op (shiftModule s M)) (op M) (-s) i (i + -s)
    rfl ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M) v).symm

omit F in
lemma scalarModuleHom_shift_square (s : ℤ) (M T : RightModule A D) :
    scalarModuleHom φ D (shiftModule s M) T ≫
      (scalarModuleShiftOppImageIso φ D
        ((scalarModuleDGFunctor φ D).op.comp
          (representable A' (ScalarExtension.rightModule φ D T))) s M).hom =
      (scalarModuleShiftOppImageIso φ D
        (representable A' (show ScalarExtension.DGBaseChange φ (RightModule A D) from T)) s M).hom ≫
          (CategoryTheory.shiftFunctor (Complex A') (-s)).map (scalarModuleHom φ D M T) :=
  scalarContraShiftComparison_naturality φ D
    (representable A' (show ScalarExtension.DGBaseChange φ (RightModule A D) from T))
    ((scalarModuleDGFunctor φ D).op.comp
      (representable A' (ScalarExtension.rightModule φ D T)))
    (fun x => (scalarModuleDGFunctor φ D).map x.unop T)
    (dgHomMap_contra_naturality (scalarModuleDGFunctor φ D) T) s M

omit F in
lemma scalarModuleHom_shift (s : ℤ) (M T : RightModule A D)
    (hM : QuasiIso (scalarModuleHom φ D M T)) :
    QuasiIso (scalarModuleHom φ D (shiftModule s M) T) := by
  have := hM
  have hs : QuasiIso (scalarModuleHom φ D (shiftModule s M) T ≫
      (scalarModuleShiftOppImageIso φ D
        ((scalarModuleDGFunctor φ D).op.comp
          (representable A' (ScalarExtension.rightModule φ D T))) s M).hom) := by
    rw [scalarModuleHom_shift_square φ D s M T]
    infer_instance
  exact quasiIso_of_comp_right (scalarModuleHom φ D (shiftModule s M) T)
    (scalarModuleShiftOppImageIso φ D
      ((scalarModuleDGFunctor φ D).op.comp
        (representable A' (ScalarExtension.rightModule φ D T))) s M).hom

omit F in
instance scalarModuleHomComparisonLocusStableUnderShift :
    (scalarModuleHomComparisonLocus φ D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    intro X hX
    apply (scalarModuleHomComparisonLocus φ D).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
    intro T
    exact scalarModuleHom_shift φ D s X.as (ForgetEnrichment.to (Complex A) T) (hX T)⟩

end SerrePositivity.DifferentialGraded
end

end ScalarHomShift

/-! ## ScalarHomCone（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomCone.lean） -/

/-! # 実際のHom係数変更比較のcone・三角形閉性 -/

@[expose] public section ScalarHomCone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Pretriangulated Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D)
    (hM : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)))
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T))) :
    QuasiIso (scalarModuleHom φ D
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) T)) :=
  scalarModuleHom_gradedSplit_middle φ D (moduleConeGradedSplit A D f) T
    (scalarModuleHom_shift φ D 1 (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T) hM) hN

lemma scalarModuleHomComparisonLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : scalarModuleHomComparisonLocus φ D T.obj₁)
    (h₂ : scalarModuleHomComparisonLocus φ D T.obj₂) :
    scalarModuleHomComparisonLocus φ D T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₂.mapIso e) h₂
  apply (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₃.mapIso e.symm)
  intro Q
  exact scalarModuleHom_cone φ D f Q (hM Q) (hN Q)

instance scalarModuleHomComparisonLocusTriangulatedClosed₃ :
    (scalarModuleHomComparisonLocus φ D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (scalarModuleHomComparisonLocus_triangle_obj₃ φ D)

instance scalarModuleHomComparisonLocusTriangulatedClosed₂ :
    (scalarModuleHomComparisonLocus φ D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

lemma scalarModuleHomComparisonLocus_zero :
    scalarModuleHomComparisonLocus φ D ((moduleToHomotopy A D).obj (moduleZero A D)) := by
  intro T
  change QuasiIso (scalarModuleHom φ D (zeroModule A D) (ForgetEnrichment.to (Complex A) T))
  have hs := moduleHom_isZero_src A D (zeroModule A D) (ForgetEnrichment.to (Complex A) T)
    (fun _ => isZero_zero (Complex A))
  have ht := moduleHom_isZero_src A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (zeroModule A D))
    (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) T))
    (fun _ => (ScalarExtension.extension φ).map_isZero (isZero_zero (Complex A)))
  have := ((ScalarExtension.extension φ).map_isZero hs).isIso ht
    (scalarModuleHom φ D (zeroModule A D) (ForgetEnrichment.to (Complex A) T))
  infer_instance

instance scalarModuleHomComparisonLocusNonempty :
    (scalarModuleHomComparisonLocus φ D).Nonempty :=
  ObjectProperty.nonempty_of_prop (scalarModuleHomComparisonLocus_zero φ D)

instance scalarModuleHomComparisonLocusContainsZero :
    (scalarModuleHomComparisonLocus φ D).ContainsZero := inferInstance

instance scalarModuleHomComparisonLocusIsTriangulated :
    (scalarModuleHomComparisonLocus φ D).IsTriangulated where

end SerrePositivity.DifferentialGraded
end

end ScalarHomCone

/-! ## ScalarPerfectHom（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarPerfectHom.lean） -/

/-! # Perfect始域に対する実際の全次数Hom係数変更比較 -/

@[expose] public section ScalarPerfectHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomComparisonLocus_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    scalarModuleHomComparisonLocus φ D ((moduleToHomotopy A D).obj M) := by
  let P := scalarModuleHomComparisonLocus φ D
  let Q := moduleToHomotopy A D
  let : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  induction c with
  | zero => exact scalarModuleHomComparisonLocus_zero φ D
  | generator x hx => exact scalarModuleHomComparisonLocus_representable φ D x
  | shift s c ih =>
      exact P.prop_of_iso ((Q.commShiftIso s).app _).symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
      let e := Q.mapIso (moduleBiprodIso A D M N) ≪≫ Q.mapBiprod M N ≪≫
        biprod.isoProd (Q.obj M) (Q.obj N)
      exact P.prop_of_iso e.symm (P.prop_prod _ _ ihc ihd)
  | cone c d f ihc ihd =>
      intro T
      exact scalarModuleHom_cone φ D f T (ihc T) (ihd T)
  | iso c e ih => exact P.prop_of_iso (Q.mapIso e) ih

lemma scalarModuleHom_quasiIso_of_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (T : ModuleCategory A D) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleHomComparisonLocus_finiteCellCode φ D c T

/-- 導来圏のperfect retractを、射影的始域のHom同値でH⁰のretractへ持ち上げる。 -/
lemma scalarModuleHom_quasiIso_of_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M))
    (T : ModuleCategory A D) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)) := by
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  apply scalarModuleHom_quasiIso_of_homotopyRetract φ D i r _ T
    (scalarModuleHom_quasiIso_of_finiteCell φ D hN T)
  apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
  rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
    Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]

/-- U13の実際のenhancementの全Homについての係数変更比較。 -/
lemma perfectScalarModuleHom_homQuasiIso (S : Set D) :
    HomQuasiIso ((ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
      (scalarModuleDGFunctor φ D)) := by
  intro M N
  change QuasiIso ((ScalarExtension.extension φ).map (𝟙 _) ≫ scalarModuleHom φ D M.val N.val)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact scalarModuleHom_quasiIso_of_perfect φ D M.property.1 M.property.2
    (ForgetEnrichment.of (Complex A) N.val)

/-- perfect指定対象のEnd比較は全Homの擬同型となる。 -/
lemma actualScalarEnd_homQuasiIso (S : Set D) (E : PerfectDGModuleOver A D S) :
    HomQuasiIso (actualScalarEnd φ D E.val) := by
  intro x y
  exact scalarModuleHom_quasiIso_of_perfect φ D E.property.1 E.property.2
    (ForgetEnrichment.of (Complex A) E.val)

end SerrePositivity.DifferentialGraded
end

end ScalarPerfectHom

/-! ## ScalarProjectiveImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarProjectiveImage.lean） -/

/-! # 実際の係数拡大によるperfect射影的加群の射影性保存 -/

@[expose] public section ScalarProjectiveImage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

instance scalarModuleExtensionAdditive : (ScalarExtension.moduleExtension φ D).Additive where
  map_add {X Y} {f g} := by
    apply moduleMorphism_ext
    intro x
    simp only [Functor.map_add, ScalarExtension.moduleExtension_eval]

lemma scalarModuleExtension_projective_shift (s : ℤ) (M : RightModule A D)
    (hM : moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj (ForgetEnrichment.of (Complex A) M))) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M))) := by
  intro N hN
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM N hN) (-s))
    (scalarModuleShiftOppImageIso φ D
      ((scalarModuleDGFunctor φ D).op.comp
        (representable A' (ForgetEnrichment.to (Complex A') N))) s M).symm

lemma scalarModuleExtension_projective_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  let F := ScalarExtension.moduleExtension φ D
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  induction c with
  | zero =>
      exact moduleHomotopicallyProjective_of_isZero A' (ScalarExtension.DGBaseChange φ D)
        (F.map_isZero (moduleZero_isZero A D))
  | generator x hx =>
      change moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
        (ForgetEnrichment.of (Complex A') (ScalarExtension.rightModule φ D (representable A x)))
      rw [scalarRepresentable_eq]
      exact representable_homotopicallyProjective A' (ScalarExtension.DGBaseChange φ D) x
  | @shift M s c ih =>
      exact scalarModuleExtension_projective_shift φ D s (ForgetEnrichment.to (Complex A) M) ih
  | @sum M N c d ihc ihd =>
      let e := F.mapIso (moduleBiprodIso A D M N) ≪≫ F.mapBiprod M N ≪≫
        (moduleBiprodIso A' (ScalarExtension.DGBaseChange φ D) (F.obj M) (F.obj N)).symm
      exact moduleHomotopicallyProjective_of_iso A' (ScalarExtension.DGBaseChange φ D) e.symm
        (moduleHomotopicallyProjective_biprod A' (ScalarExtension.DGBaseChange φ D) ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact (scalarModuleGradedSplit φ D (moduleConeGradedSplit A D f)).homotopicallyProjective
        A' (ScalarExtension.DGBaseChange φ D) ihd
          (scalarModuleExtension_projective_shift φ D 1 (ForgetEnrichment.to (Complex A) M) ihc)
  | iso c e ih =>
      exact moduleHomotopicallyProjective_of_iso A' (ScalarExtension.DGBaseChange φ D)
        (F.mapIso e) ih

lemma scalarModuleExtension_projective_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleExtension_projective_finiteCellCode φ D c

lemma scalarModuleExtension_projective_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M)) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  let F := ScalarExtension.moduleExtension φ D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  apply moduleHomotopicallyProjective_of_homotopyRetract A'
    (ScalarExtension.DGBaseChange φ D) (F.map i) (F.map r) _
      (scalarModuleExtension_projective_finiteCell φ D hN)
  have he := congrArg (scalarModuleExtensionHomotopy φ D).map h
  change (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map (F.map (i ≫ r)) =
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map (F.map (𝟙 M)) at he
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he

end SerrePositivity.DifferentialGraded
end

end ScalarProjectiveImage

/-! ## ScalarShiftCoherence（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarShiftCoherence.lean） -/

/-! # 実際の加群係数拡大の正規化されたshift比較 -/

@[expose] public section ScalarShiftCoherence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedScalarModuleShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (ScalarExtension.rightModule φ D (shiftModule s M)).map x y ≫
        homPostcompose ((ScalarExtension.rightModule φ D (shiftModule s M)).obj x)
          (((ScalarExtension.extension φ).commShiftIso s).app (M.obj y)).hom =
      (shiftModule s (ScalarExtension.rightModule φ D M)).map x y ≫
        homPrecompose (((ScalarExtension.extension φ).commShiftIso s).app (M.obj x)).hom
          ((shiftModule s (ScalarExtension.rightModule φ D M)).obj y) := by
  apply moduleShiftRepresentation_naturality A' (ScalarExtension.DGBaseChange φ D) s
    (scalarModuleHomElement φ D (normalizedModuleShiftOut A D s M))
  intro x i
  have h := congrArg (fun z => z.v i (i + s) rfl)
    (scalarModuleHomElement_π_map φ D (normalizedModuleShiftOut A D s M) x.unop)
  simp only [Cochain.map_v, normalizedModuleShiftOut_v, CategoryTheory.Functor.map_id] at h
  change 𝟙 _ = _
  exact h.symm

/-- 評価成分が通常の複体系数変更のshift比較となる正規化同型。 -/
def normalizedScalarModuleExtensionShiftIso (s : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A') (shiftModule s (ScalarExtension.rightModule φ D M)) :=
  moduleIsoMk A' (ScalarExtension.DGBaseChange φ D)
    (fun x => ((ScalarExtension.extension φ).commShiftIso s).app (M.obj x))
    (normalizedScalarModuleShift_naturality φ D s M)

lemma normalizedScalarModuleExtensionShiftIso_hom_eval_f (s : ℤ) (M : RightModule A D)
    (x : ScalarExtension.DGBaseChange φ D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      (normalizedScalarModuleExtensionShiftIso φ D s M).hom).f i = 𝟙 _ := by
  rw [normalizedScalarModuleExtensionShiftIso, moduleIsoMk_hom_eval]
  rfl

lemma normalizedScalarModuleExtensionShiftIso_naturality (s : ℤ)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (ScalarExtension.moduleExtension φ D).map ((moduleShiftFunctor A D s).map f) ≫
        (normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) N)).hom =
      (normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) M)).hom ≫
        (moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s).map
          ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, comp_f, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f,
    ScalarExtension.moduleExtension_eval]
  have hs := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i)
    (moduleShiftFunctor_map_eval A D s f (show D from x))
  have ht := congrArg (fun k => k.f i)
    (moduleShiftFunctor_map_eval A' (ScalarExtension.DGBaseChange φ D) s
      ((ScalarExtension.moduleExtension φ D).map f) x)
  have he := congrArg (fun k => k.f (i + s)) (ScalarExtension.moduleExtension_eval φ D f x)
  exact hs.trans (he.symm.trans ht.symm)

def normalizedScalarModuleExtensionShiftNatIso (s : ℤ) :
    moduleShiftFunctor A D s ⋙ ScalarExtension.moduleExtension φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s :=
  NatIso.ofComponents
    (F := moduleShiftFunctor A D s ⋙ ScalarExtension.moduleExtension φ D)
    (G := ScalarExtension.moduleExtension φ D ⋙
      moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s)
    (fun M => normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) M))
    (fun {M N} f =>
      normalizedScalarModuleExtensionShiftIso_naturality φ D s (M := M) (N := N) f)

def normalizedScalarModuleExtensionCommShiftIso (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s ⋙ ScalarExtension.moduleExtension φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        CategoryTheory.shiftFunctor (ModuleCategory A' (ScalarExtension.DGBaseChange φ D)) s := by
  rw [moduleShiftFunctor_eq, moduleShiftFunctor_eq]
  exact normalizedScalarModuleExtensionShiftNatIso φ D s

lemma normalizedScalarModuleExtensionShiftNatIso_zero :
    normalizedScalarModuleExtensionShiftNatIso φ D 0 =
      CategoryTheory.Functor.CommShift.isoZero (ScalarExtension.moduleExtension φ D) ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  change ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
    (normalizedScalarModuleExtensionShiftIso φ D 0 (ForgetEnrichment.to (Complex A) M)).hom).f i = _
  rw [normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D 0
    (ForgetEnrichment.to (Complex A) M) x i]
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app,
    CategoryTheory.Functor.map_comp, comp_f, moduleShiftZero_eq A D,
    moduleShiftZero_eq A' (ScalarExtension.DGBaseChange φ D)]
  rw [ScalarExtension.moduleExtension_eval φ D ((moduleShiftZeroIso A D).hom.app M) x,
    moduleShiftZeroIso_hom_eval A D M (show D from x),
    moduleShiftZeroIso_inv_eval A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) x]
  have h := congrArg (fun e => (e.hom.app
    ((moduleEvaluation A D (show D from x)).obj M)).f i)
    ((ScalarExtension.extension φ).commShiftIso_zero ℤ)
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app, comp_f] at h
  exact h

lemma normalizedScalarModuleExtensionCommShiftIso_zero :
    normalizedScalarModuleExtensionCommShiftIso φ D 0 =
      CategoryTheory.Functor.CommShift.isoZero (ScalarExtension.moduleExtension φ D) ℤ :=
  normalizedScalarModuleExtensionShiftNatIso_zero φ D

end SerrePositivity.DifferentialGraded
end

end ScalarShiftCoherence

/-! ## ScalarShiftAddition（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarShiftAddition.lean） -/

/-! # 実際の係数拡大の正規化shift比較の加法整合性 -/

@[expose] public section ScalarShiftAddition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarComplexShiftAdd_hom_f (K : Complex A) (s t i : ℤ) :
    ((ScalarExtension.extension φ).map ((shiftFunctorAdd (Complex A) s t).hom.app K)).f i =
      ((shiftFunctorAdd (Complex A') s t).hom.app ((ScalarExtension.extension φ).obj K)).f i := by
  change (ModuleCat.extendScalars φ).map
    (((shiftFunctorAdd (Complex A) s t).hom.app K).f i) = _
  rw [shiftFunctorAdd_hom_app_f, shiftFunctorAdd_hom_app_f]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedScalarModuleExtensionShiftIso_add_square (s t : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).map (moduleShiftAddIsoObj A D s t M).hom ≫
        (normalizedScalarModuleExtensionShiftIso φ D t (shiftModule s M)).hom ≫
        (moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) t).map
          (normalizedScalarModuleExtensionShiftIso φ D s M).hom =
      (normalizedScalarModuleExtensionShiftIso φ D (s + t) M).hom ≫
        (moduleShiftAddIsoObj A' (ScalarExtension.DGBaseChange φ D) s t
          (ScalarExtension.rightModule φ D M)).hom := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, comp_f, comp_f, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D t (shiftModule s M) x i,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D (s + t) M x i]
  have hm := congrArg (fun k => k.f i)
    (moduleShiftFunctor_map_eval A' (ScalarExtension.DGBaseChange φ D) t
      (normalizedScalarModuleExtensionShiftIso φ D s M).hom x)
  have hm' : ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      ((moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) t).map
        (normalizedScalarModuleExtensionShiftIso φ D s M).hom)).f i = 𝟙 _ :=
    hm.trans (normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D s M x (i + t))
  rw [hm']
  simp only [Category.id_comp]
  have hF := congrArg (fun k => k.f i)
    (ScalarExtension.moduleExtension_eval φ D (moduleShiftAddIsoObj A D s t M).hom x)
  have hs := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i)
    (moduleShiftAddIsoObj_hom_eval A D s t M (show D from x))
  have ht := congrArg (fun k => k.f i)
    (moduleShiftAddIsoObj_hom_eval A' (ScalarExtension.DGBaseChange φ D) s t
      (ScalarExtension.rightModule φ D M) x)
  exact hF.trans (hs.trans ((scalarComplexShiftAdd_hom_f φ (M.obj (op x)) s t i).trans ht.symm))

lemma normalizedScalarModuleExtensionShiftNatIso_add (s t : ℤ) :
    normalizedScalarModuleExtensionShiftNatIso φ D (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
        (A := ℤ) (F := ScalarExtension.moduleExtension φ D) (a := s) (b := t)
        (normalizedScalarModuleExtensionShiftNatIso φ D s)
        (normalizedScalarModuleExtensionShiftNatIso φ D t) := by
  apply shiftComparison_eq_isoAdd_of_square
    (C := ModuleCategory A D) (E := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
    (ScalarExtension.moduleExtension φ D) s t
    (normalizedScalarModuleExtensionShiftNatIso φ D s)
    (normalizedScalarModuleExtensionShiftNatIso φ D t)
    (normalizedScalarModuleExtensionShiftNatIso φ D (s + t))
  intro M
  simp only [moduleShiftAdd_eq A D, moduleShiftAdd_eq A' (ScalarExtension.DGBaseChange φ D),
    moduleShiftFunctor_eq A D, moduleShiftFunctor_eq A' (ScalarExtension.DGBaseChange φ D),
    normalizedScalarModuleExtensionShiftNatIso]
  exact normalizedScalarModuleExtensionShiftIso_add_square φ D s t
    (ForgetEnrichment.to (Complex A) M)

lemma normalizedScalarModuleExtensionCommShiftIso_add (s t : ℤ) :
    normalizedScalarModuleExtensionCommShiftIso φ D (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
        (A := ℤ) (F := ScalarExtension.moduleExtension φ D) (a := s) (b := t)
        (normalizedScalarModuleExtensionCommShiftIso φ D s)
        (normalizedScalarModuleExtensionCommShiftIso φ D t) :=
  normalizedScalarModuleExtensionShiftNatIso_add φ D s t

/-- 零・加法shiftと整合する、実際の加群係数拡大の比較データ。 -/
@[instance_reducible]
def scalarModuleExtensionCommShift : (ScalarExtension.moduleExtension φ D).CommShift ℤ where
  commShiftIso := normalizedScalarModuleExtensionShiftNatIso φ D
  commShiftIso_zero := normalizedScalarModuleExtensionShiftNatIso_zero φ D
  commShiftIso_add := normalizedScalarModuleExtensionShiftNatIso_add φ D

end SerrePositivity.DifferentialGraded
end

end ScalarShiftAddition

/-! ## ScalarHomotopyShift（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomotopyShift.lean） -/

/-! # 実際の係数拡大の整合的shift比較を主Kへ降ろす -/

@[expose] public section ScalarHomotopyShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

@[instance_reducible]
def scalarModuleExtensionHomotopyCommShift :
    (scalarModuleExtensionHomotopy φ D).CommShift ℤ := by
  letI := scalarModuleExtensionCommShift φ D
  unfold scalarModuleExtensionHomotopy
  infer_instance

def scalarModuleExtensionHomotopyFacIso :
    moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D) :=
  Quotient.lift.isLift _ _ _

lemma scalarModuleExtensionHomotopyFacIso_commShift :
    letI := scalarModuleExtensionCommShift φ D
    letI := scalarModuleExtensionHomotopyCommShift φ D
    NatTrans.CommShift (scalarModuleExtensionHomotopyFacIso φ D).hom ℤ := by
  let := scalarModuleExtensionCommShift φ D
  let := scalarModuleExtensionHomotopyCommShift φ D
  unfold scalarModuleExtensionHomotopyFacIso
  exact Quotient.liftCommShift_compatibility _ _ _ _

end SerrePositivity.DifferentialGraded
end

end ScalarHomotopyShift

/-! ## ScalarConeTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarConeTriangles.lean） -/

/-! # 実際の係数拡大のcone連結射と三角形の比較 -/

@[expose] public section ScalarConeTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex Pretriangulated
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleExtensionConeComparison_fst_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      (scalarModuleExtensionConeComparison φ D f)).f i ≫
        (((mappingCone.fst ((moduleEvaluation A D x).map f)).val.map
          (ModuleCat.extendScalars φ)).v i (i + 1) rfl) =
      (mappingCone.fst ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
        ((ScalarExtension.moduleExtension φ D).map f))).val.v i (i + 1) rfl := by
  rw [scalarModuleExtensionConeComparison, moduleConeDescOfBoundary_eval]
  let L := ModuleCat.extendScalars φ
  let g := (moduleEvaluation A D x).map f
  have hα := scalarModuleHomElement_π_map φ D (moduleConeInlElement A D f) x
  rw [moduleConeInlElement_π] at hα
  have hβ := ScalarExtension.moduleExtension_eval φ D (moduleConeInr A D f) x
  rw [moduleConeInr_eval] at hβ
  apply complexConeDesc_fst A' _ _ _ ((mappingCone.fst g).val.map L)
  · apply (congrArg (fun z => z.comp ((mappingCone.fst g).val.map L) (neg_add_cancel 1)) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inl_fst g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inr_fst g)

lemma scalarModuleExtensionConnecting_eval_f {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      ((ScalarExtension.moduleExtension φ D).map (moduleConeConnecting A D f) ≫
        (normalizedScalarModuleExtensionShiftIso φ D 1
          (ForgetEnrichment.to (Complex A) M)).hom)).f i =
      -(((mappingCone.fst ((moduleEvaluation A D x).map f)).val.map
        (ModuleCat.extendScalars φ)).v i (i + 1) rfl) := by
  rw [CategoryTheory.Functor.map_comp, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D 1
      (ForgetEnrichment.to (Complex A) M) x i]
  have he := ScalarExtension.moduleExtension_eval φ D (moduleConeConnecting A D f) x
  have hs := moduleConeConnecting_eval A D f x
  have h := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i) hs
  apply (congrArg (fun k => k.f i) he).trans
  apply h.trans
  change (ModuleCat.extendScalars φ).map ((mappingCone.triangle
    ((moduleEvaluation A D x).map f)).mor₃.f i) = _
  simp only [SerrePositivity.coneTriangle_mor₃_f, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id, CategoryTheory.Functor.map_neg, Cochain.map_v]

lemma scalarModuleExtensionConeComparison_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleExtensionConeComparison φ D f ≫
        (ScalarExtension.moduleExtension φ D).map (moduleConeConnecting A D f) ≫
          (normalizedScalarModuleExtensionShiftIso φ D 1 (ForgetEnrichment.to (Complex A) M)).hom =
      moduleConeConnecting A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, comp_f,
    scalarModuleExtensionConnecting_eval_f φ D f (show D from x) i,
    moduleConeConnecting_eval A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f) x,
    SerrePositivity.coneTriangle_mor₃_f]
  simp only [Preadditive.comp_neg, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  exact congrArg Neg.neg (scalarModuleExtensionConeComparison_fst_eval φ D f (show D from x) i)

local instance : (ScalarExtension.moduleExtension φ D).CommShift ℤ :=
  scalarModuleExtensionCommShift φ D

def scalarModuleExtensionConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeTriangle A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) ≅
      (ScalarExtension.moduleExtension φ D).mapTriangle.obj (moduleConeTriangle A D f) :=
  coneTriangleMapIso (ScalarExtension.moduleExtension φ D) f
    (moduleConeInr A D f) (moduleConeConnecting A D f)
    (moduleConeInr A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (moduleConeConnecting A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (scalarModuleExtensionConeIso φ D f)
    (scalarModuleExtensionConeComparison_inr φ D f)
    (scalarModuleExtensionConeComparison_connecting φ D f)

local instance : (scalarModuleExtensionHomotopy φ D).CommShift ℤ :=
  scalarModuleExtensionHomotopyCommShift φ D

def scalarModuleExtensionHomotopyConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (scalarModuleExtensionHomotopy φ D).mapTriangle.obj (moduleHomotopyConeTriangle A D f) ≅
      moduleHomotopyConeTriangle A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) := by
  let := scalarModuleExtensionHomotopyFacIso_commShift φ D
  exact mapTriangleSquareIso (moduleToHomotopy A D) (scalarModuleExtensionHomotopy φ D)
    (ScalarExtension.moduleExtension φ D)
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D))
    (scalarModuleExtensionHomotopyFacIso φ D)
    (moduleConeTriangle A D f)
    (moduleConeTriangle A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (scalarModuleExtensionConeTriangleIso φ D f).symm

lemma scalarModuleExtensionHomotopyIsTriangulated :
    (scalarModuleExtensionHomotopy φ D).IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _
      (moduleHomotopyConeTriangle_distinguished A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f)) _
      ((scalarModuleExtensionHomotopy φ D).mapTriangle.mapIso e ≪≫
        scalarModuleExtensionHomotopyConeTriangleIso φ D f)

end SerrePositivity.DifferentialGraded
end

end ScalarConeTriangles

/-! ## ScalarModuleShiftImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleShiftImage.lean） -/

/-! # 実際の加群係数拡大と整数shiftの比較同型 -/

@[expose] public section ScalarModuleShiftImage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D)) (Complex A'))

def scalarModuleShiftImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (shiftModule s M)) (F.obj M) s :=
  let := φ.toAlgebra
  (F.map (shiftModule s M) M).f s ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)

def scalarModuleShiftImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj M) (F.obj (shiftModule s M)) (-s) :=
  let := φ.toAlgebra
  (F.map M (shiftModule s M)).f (-s) ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)

lemma scalarModuleShiftImageOut_d (s : ℤ) (M : RightModule A D) :
    δ s (s + 1) (scalarModuleShiftImageOut φ D F s M) = 0 := by
  let := φ.toAlgebra
  have h := F.map_d_cochain A' (x := shiftModule s M) (y := M)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M) (q := s + 1)
  have hz : (F.map (shiftModule s M) M).f (s + 1)
      ((ModuleCat.extendScalars φ).map ((moduleHom A D (shiftModule s M) M).d s (s + 1))
        ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)) = 0 := by
    erw [ModuleCat.ExtendScalars.map_tmul φ]
    rw [moduleShiftOutElement_d, TensorProduct.tmul_zero, map_zero]
  exact h.symm.trans hz

lemma scalarModuleShiftImageOutIn (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftImageOut φ D F s M).comp (scalarModuleShiftImageIn φ D F s M)
      (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (shiftModule s M))) := by
  let := φ.toAlgebra
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := shiftModule s M) (y := M) (z := shiftModule s M)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M) (add_neg_cancel s)
  have he := congrArg (fun z : GradedHom A (shiftModule s M) (shiftModule s M) 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftOutIn A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) (shiftModule s M)
  have h := congrArg (fun z => (F.map (shiftModule s M) (shiftModule s M)).f 0 z)
    (hc.trans (he.trans hu.symm))
  rw [DGFunctor.map_compose_cochain, F.map_unitElement A', Bimodule.complex_unitElement] at h
  exact h

lemma scalarModuleShiftImageInOut (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftImageIn φ D F s M).comp (scalarModuleShiftImageOut φ D F s M)
      (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj M)) := by
  let := φ.toAlgebra
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := M) (y := shiftModule s M) (z := M)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M) (neg_add_cancel s)
  have he := congrArg (fun z : GradedHom A M M 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftInOut A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) M
  have h := congrArg (fun z => (F.map M M).f 0 z) (hc.trans (he.trans hu.symm))
  rw [DGFunctor.map_compose_cochain, F.map_unitElement A', Bimodule.complex_unitElement] at h
  exact h

def scalarModuleShiftImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ≅ (F.obj M)⟦s⟧ :=
  complexShiftIso A' (scalarModuleShiftImageOut φ D F s M)
    (scalarModuleShiftImageOut_d φ D F s M) (scalarModuleShiftImageIn φ D F s M)
    (scalarModuleShiftImageOutIn φ D F s M) (scalarModuleShiftImageInOut φ D F s M)

omit F in
lemma scalarModuleExtensionShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (ScalarExtension.rightModule φ D (shiftModule s M)).map x y ≫
        homPostcompose ((ScalarExtension.rightModule φ D (shiftModule s M)).obj x)
          (scalarModuleShiftImageIso φ D
            ((scalarModuleDGFunctor φ D).comp
              (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) y.unop)) s M).hom =
      (shiftModule s (ScalarExtension.rightModule φ D M)).map x y ≫
        homPrecompose
          (scalarModuleShiftImageIso φ D ((scalarModuleDGFunctor φ D).comp
            (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x.unop)) s M).hom
          ((shiftModule s (ScalarExtension.rightModule φ D M)).obj y) := by
  apply moduleShiftRepresentation_naturality A' (ScalarExtension.DGBaseChange φ D) s
    (scalarModuleHomElement φ D (moduleShiftOutElement A D s M))
  intro x i
  change (complexShiftComparison A' _ _).f i = _
  rw [complexShiftComparison_f]
  rfl

omit F in
/-- 全次数自然な加群同型としての、実際の係数拡大と整数shiftの比較。 -/
def scalarModuleExtensionShiftIso (s : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A') (shiftModule s (ScalarExtension.rightModule φ D M)) :=
  moduleIsoMk A' (ScalarExtension.DGBaseChange φ D)
    (fun x => scalarModuleShiftImageIso φ D ((scalarModuleDGFunctor φ D).comp
      (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x.unop)) s M)
    (scalarModuleExtensionShift_naturality φ D s M)

end SerrePositivity.DifferentialGraded
end

end ScalarModuleShiftImage

/-! ## ScalarPerfectImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarPerfectImage.lean） -/

/-! # 実際の係数拡大は指定生成集合からのperfect対象を保つ -/

@[expose] public section ScalarPerfectImage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更したdg圏で、元と同じ指定対象を生成元として取る。 -/
def scalarPerfectGenerators (S : Set D) : Set (ScalarExtension.DGBaseChange φ D) :=
  fun x => (show D from x) ∈ S

lemma scalarModuleExtension_perfect_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  let F := ScalarExtension.moduleExtension φ D
  let Q := moduleToDerived A' (ScalarExtension.DGBaseChange φ D)
  let G := F ⋙ Q
  let P := modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  induction c with
  | zero => exact P.prop_of_isZero (Q.map_isZero (F.map_isZero (moduleZero_isZero A D)))
  | generator x hx =>
      change P (Q.obj (ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ D (representable A x))))
      rw [scalarRepresentable_eq]
      exact modulePerfectOver_representable A' (ScalarExtension.DGBaseChange φ D) x hx
  | @shift M s c ih =>
      let e := Q.mapIso (scalarModuleExtensionShiftIso φ D s
        (ForgetEnrichment.to (Complex A) M)) ≪≫ (Q.commShiftIso s).app (F.obj M)
      exact P.prop_of_iso e.symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
      let e := G.mapIso (moduleBiprodIso A D M N) ≪≫ G.mapBiprod M N ≪≫
        biprod.isoProd (G.obj M) (G.obj N)
      exact P.prop_of_iso e.symm (P.prop_prod _ _ ihc ihd)
  | @cone M N c d f ihc ihd =>
      have hc := P.ext_of_isTriangulatedClosed₃
        (moduleDerivedConeTriangle A' (ScalarExtension.DGBaseChange φ D) (F.map f))
        (moduleDerivedConeTriangle_distinguished A' (ScalarExtension.DGBaseChange φ D) (F.map f))
        ihc ihd
      exact P.prop_of_iso (Q.mapIso (scalarModuleExtensionConeIso φ D f)) hc
  | iso c e ih => exact P.prop_of_iso (G.mapIso e) ih

lemma scalarModuleExtension_perfect_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleExtension_perfect_finiteCellCode φ D c

lemma scalarModuleExtension_perfect_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M)) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M)) := by
  let F := ScalarExtension.moduleExtension φ D
  let Q := moduleToHomotopy A D
  let Q' := moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)
  let H := scalarModuleExtensionHomotopy φ D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  let b : Retract (Q'.obj (F.obj M)) (Q'.obj (F.obj N)) :=
    { i := Q'.map (F.map i)
      r := Q'.map (F.map r)
      retract := by
        have he := congrArg H.map h
        change Q'.map (F.map (i ≫ r)) = Q'.map (F.map (𝟙 M)) at he
        simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he }
  let L := moduleHomotopyToDerivedClosed A' (ScalarExtension.DGBaseChange φ D)
  let e := moduleToHomotopyDerivedIso A' (ScalarExtension.DGBaseChange φ D)
  let b' := (Retract.ofIso (e.app (F.obj M)).symm).trans
    ((b.map L).trans (Retract.ofIso (e.app (F.obj N))))
  exact modulePerfectOver_of_retract A' (ScalarExtension.DGBaseChange φ D) b'
    (scalarModuleExtension_perfect_finiteCell φ D hN)

end SerrePositivity.DifferentialGraded
end

end ScalarPerfectImage
