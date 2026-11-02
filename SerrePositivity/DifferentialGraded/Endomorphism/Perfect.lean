module

public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Module.ConeMaps
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors

/-!
# Endomorphism.Perfect

## 概要
17 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ConeConnectingComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ConeConnectingComparison.lean） -/

/-! # 正規化shift比較と標準coneの連結射 -/

@[expose] public section ConeConnectingComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    forward A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (y := shiftModule 1 (ForgetEnrichment.to (Complex A) M))
      (z := ForgetEnrichment.to (Complex A) M)
      (endomorphismClosedElement A D (moduleConeConnecting A D f))
      (normalizedModuleShiftOut A D 1 (ForgetEnrichment.to (Complex A) M)) (zero_add 1) =
        -moduleConeFstElement A D f := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (shiftModule 1 (ForgetEnrichment.to (Complex A) M)) x).f 0
        (endomorphismClosedElement A D (moduleConeConnecting A D f)) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeConnecting A D f)) :=
    endomorphismClosedElement_π A D (moduleConeConnecting A D f) x
  rw [moduleHomForward_π, map_neg, moduleConeFstElement_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  erw [hπ]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    normalizedModuleShiftOut_v_eq, moduleConeConnecting_eval,
    SerrePositivity.coneTriangle_mor₃_f]
  simp only [shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
    Preadditive.neg_comp]
  exact congrArg Neg.neg (Cochain.v_comp_XIsoOfEq_hom _ i (i + 1) j rfl hij)

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctorConnecting_eval_f {M N : ModuleCategory A D} (f : M ⟶ N)
    (b : B) (i : ℤ) :
    ((moduleEvaluation A B b).map (F.onClosed.map (moduleConeConnecting A D f) ≫
      (normalizedDGModuleFunctorShiftIso A D B F 1 (ForgetEnrichment.to (Complex A) M)).hom)).f i =
      -(DGFunctor.moduleConeImageFst A D (F.comp (moduleEvaluationDG A B b)) f).v
        i (i + 1) rfl := by
  let G := F.comp (moduleEvaluationDG A B b)
  have h := congrArg (fun z => (G.map
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) M)).f 1 z)
      (normalizedModuleShiftOut_connecting A D f)
  rw [G.map_forward_cochain A, map_neg] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  have hc : (G.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (shiftModule 1 (ForgetEnrichment.to (Complex A) M))).f 0
      (endomorphismClosedElement A D (moduleConeConnecting A D f)) =
      Cochain.ofHom ((G.toComplexFunctor A).map (moduleConeConnecting A D f)) :=
    G.map_closedElement A (moduleConeConnecting A D f)
  rw [hc] at h
  have hv := Cochain.congr_v h i (i + 1) rfl
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.neg_v] at hv
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  exact hv

lemma dgModuleFunctorConeComparison_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    dgModuleFunctorConeComparison A D B F f ≫ F.onClosed.map (moduleConeConnecting A D f) ≫
      (normalizedDGModuleFunctorShiftIso A D B F 1 (ForgetEnrichment.to (Complex A) M)).hom =
        moduleConeConnecting A B (F.onClosed.map f) := by
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgModuleFunctorConnecting_eval_f, dgModuleFunctorConeComparison_eval,
    moduleConeConnecting_eval, SerrePositivity.coneTriangle_mor₃_f]
  simp only [Preadditive.comp_neg, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  let G := F.comp (moduleEvaluationDG A B b)
  exact congrArg Neg.neg (complexConeDesc_fst A ((G.toComplexFunctor A).map f)
    (DGFunctor.moduleConeImageInl A D G f)
    ((G.toComplexFunctor A).map (moduleConeInr A D f))
    (DGFunctor.moduleConeImageFst A D G f) (DGFunctor.moduleConeImageInl_d A D G f)
    (DGFunctor.moduleConeImage_inl_fst A D G f)
    (DGFunctor.moduleConeImage_inr_fst A D G f) i)

end SerrePositivity.DifferentialGraded
end

end ConeConnectingComparison

/-! ## ConeTriangleComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ConeTriangleComparison.lean） -/

/-! # 加群値dg関手の標準cone三角形比較と主Kでの三角性 -/

@[expose] public section ConeTriangleComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))
local instance : F.onClosed.CommShift ℤ := dgModuleFunctorCommShift A D B F

/-- 正規化shift比較を用いた標準cone三角形の同型。 -/
def dgModuleFunctorConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeTriangle A B (F.onClosed.map f) ≅
      F.onClosed.mapTriangle.obj (moduleConeTriangle A D f) :=
  Triangle.isoMk (moduleConeTriangle A B (F.onClosed.map f))
    (F.onClosed.mapTriangle.obj (moduleConeTriangle A D f))
    (Iso.refl (F.onClosed.obj M)) (Iso.refl (F.onClosed.obj N))
    (dgModuleFunctorConeIso A D B F f)
    (by
      change F.onClosed.map f ≫ 𝟙 (F.onClosed.obj N) =
        𝟙 (F.onClosed.obj M) ≫ F.onClosed.map f
      rw [Category.comp_id, Category.id_comp])
    (by
      change moduleConeInr A B (F.onClosed.map f) ≫ dgModuleFunctorConeComparison A D B F f =
        𝟙 (F.onClosed.obj N) ≫ F.onClosed.map (moduleConeInr A D f)
      rw [Category.id_comp]
      exact dgModuleFunctorConeComparison_inr A D B F f)
    (by
      change moduleConeConnecting A B (F.onClosed.map f) ≫
        (CategoryTheory.shiftFunctor (ModuleCategory A B) (1 : ℤ)).map
          (𝟙 (F.onClosed.obj M)) =
        dgModuleFunctorConeComparison A D B F f ≫ F.onClosed.map (moduleConeConnecting A D f) ≫
          (normalizedDGModuleFunctorCommShiftIso A D B F 1).hom.app M
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      have he : (normalizedDGModuleFunctorCommShiftIso A D B F 1).hom.app M =
          (normalizedDGModuleFunctorShiftIso A D B F 1
            (ForgetEnrichment.to (Complex A) M)).hom := by
        simp only [normalizedDGModuleFunctorCommShiftIso, moduleShiftFunctor_eq]
        rfl
      rw [he]
      exact (dgModuleFunctorConeComparison_connecting A D B F f).symm)

local instance : F.onHomotopy.CommShift ℤ := dgModuleFunctorHomotopyCommShift A D B F

/-- 主Kの標準cone三角形の比較。因子分解自然同型のshift整合性を用いる。 -/
def dgModuleFunctorHomotopyConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    F.onHomotopy.mapTriangle.obj (moduleHomotopyConeTriangle A D f) ≅
      moduleHomotopyConeTriangle A B (F.onClosed.map f) := by
  letI := dgModuleFunctorHomotopyFacIso_commShift A D B F
  exact mapTriangleSquareIso (moduleToHomotopy A D) F.onHomotopy F.onClosed
    (moduleToHomotopy A B) (dgModuleFunctorHomotopyFacIso A D B F)
    (moduleConeTriangle A D f) (moduleConeTriangle A B (F.onClosed.map f))
    (dgModuleFunctorConeTriangleIso A D B F f).symm

/-- 加群値dg関手の主K関手は正規化したshift構造について三角関手である。 -/
lemma dgModuleFunctorHomotopyIsTriangulated : F.onHomotopy.IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _ (moduleHomotopyConeTriangle_distinguished A B
      (F.onClosed.map f)) _
      (F.onHomotopy.mapTriangle.mapIso e ≪≫ dgModuleFunctorHomotopyConeTriangleIso A D B F f)

end SerrePositivity.DifferentialGraded
end

end ConeTriangleComparison

/-! ## DerivedHomHomotopyComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedHomHomotopyComparison.lean） -/

/-! # 主Kの再構成Homと主導来Homの全射自然な比較 -/

@[expose] public section DerivedHomHomotopyComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

/-- dg HomをKへ送って局所化する経路と、局所化して導来Homを取る経路の自然同型。 -/
def endomorphismDerivedHomHomotopyIso :
    (endomorphismModuleHom A D E).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A (EndomorphismObject E) ≅
      moduleHomotopyToDerivedClosed A D ⋙ endomorphismDerivedHom A D E hE :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    ((Functor.associator (moduleToHomotopy A D) (endomorphismModuleHom A D E).onHomotopy
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E))).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (endomorphismModuleHom A D E).onHomotopy_fac)
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E)) ≪≫
      Functor.associator (endomorphismModuleHom A D E).onClosed
        (moduleToHomotopy A (EndomorphismObject E))
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E)) ≪≫
      Functor.isoWhiskerLeft (endomorphismModuleHom A D E).onClosed
        (moduleToHomotopyDerivedIso A (EndomorphismObject E)) ≪≫
      (eqToIso (endomorphismDerivedHom_fac A D E hE)).symm ≪≫
      Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A D).symm
        (endomorphismDerivedHom A D E hE) ≪≫
      Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
        (endomorphismDerivedHom A D E hE))

variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

lemma perfectEndomorphismDG_homotopy_inclusion_square :
    (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy =
      (perfectDGModuleInclusion A D S).onHomotopy ⋙
        (endomorphismModuleHom A D E.val).onHomotopy := by
  rw [← DGFunctor.onHomotopy_comp, ← DGFunctor.onHomotopy_comp]
  exact congrArg DGFunctor.onHomotopy (perfectEndomorphismDG_inclusion_square A D S E hgen)

/-- U13のenhancement比較と主導来HomのPerf制限の、導来圏内での自然な正方形。 -/
def perfectEndomorphismDerivedComparisonUnderlying :
    ((perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ) ⋙
          perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      (perfectDGModuleToPerfect A D S ⋙ perfectEndomorphismHomToPerfect A D S E hgen) ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ :=
  Functor.isoWhiskerRight
      (eqToIso (perfectEndomorphismDG_homotopy_inclusion_square A D S E hgen))
      (moduleHomotopyToDerivedClosed A (EndomorphismObject E.val)) ≪≫
    Functor.associator (perfectDGModuleInclusion A D S).onHomotopy
      (endomorphismModuleHom A D E.val).onHomotopy
      (moduleHomotopyToDerivedClosed A (EndomorphismObject E.val)) ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleInclusion A D S).onHomotopy
      (endomorphismDerivedHomHomotopyIso A D E.val E.property.1) ≪≫
    (Functor.associator (perfectDGModuleInclusion A D S).onHomotopy
      (moduleHomotopyToDerivedClosed A D) (endomorphismDerivedHom A D E.val E.property.1)).symm

/-- 充満部分圏への包含の完全忠実性により、正方形をPerf自体の自然同型として保持する。 -/
def perfectEndomorphismDerivedComparison :
    (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ≅
      perfectDGModuleToPerfect A D S ⋙ perfectEndomorphismHomToPerfect A D S E hgen := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full := by
    unfold perfectModuleInclusion
    infer_instance
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful := by
    unfold perfectModuleInclusion
    infer_instance
  exact Functor.fullyFaithfulCancelRight
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ)
    (perfectEndomorphismDerivedComparisonUnderlying A D S E hgen)

/-- 主Perf上の導来Homを、U13のenhancement同値の逆とdg比較を用いて計算する。 -/
def perfectEndomorphismHomToPerfectViaEnhancement :
    perfectEndomorphismHomToPerfect A D S E hgen ≅
      (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        ((perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
          perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ) :=
  (perfectEndomorphismHomToPerfect A D S E hgen).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).counitIso.symm
      (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
    Functor.associator (perfectDGModuleHomotopyEquivalence A D S).inverse
      (perfectDGModuleHomotopyEquivalence A D S).functor
      (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleHomotopyEquivalence A D S).inverse
      (perfectEndomorphismDerivedComparison A D S E hgen).symm

instance perfectEndomorphismHomToPerfectFull :
    (perfectEndomorphismHomToPerfect A D S E hgen).Full :=
  Functor.Full.of_iso (perfectEndomorphismHomToPerfectViaEnhancement A D S E hgen).symm

instance perfectEndomorphismHomToPerfectFaithful :
    (perfectEndomorphismHomToPerfect A D S E hgen).Faithful :=
  Functor.Faithful.of_iso (perfectEndomorphismHomToPerfectViaEnhancement A D S E hgen).symm

end SerrePositivity.DifferentialGraded
end

end DerivedHomHomotopyComparison

/-! ## DerivedShiftCoherence（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedShiftCoherence.lean） -/

/-! # 導来Homの整合的shift比較 -/

@[expose] public section DerivedShiftCoherence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

instance endomorphismDerivedHomLifting :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
      (endomorphismDerivedHom A D E hE) :=
  ⟨eqToIso (endomorphismDerivedHom_fac A D E hE)⟩

/-- 導来Homのshift構造。全Hom写像の正規化比較とzero/add coherenceを局所化する。 -/
@[instance_reducible]
def endomorphismDerivedHomCommShift : (endomorphismDerivedHom A D E hE).CommShift ℤ := by
  letI := dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
  exact Functor.commShiftOfLocalization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismDerivedHom A D E hE)

section
local instance : (endomorphismModuleHom A D E).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE

lemma endomorphismDerivedHomFac_commShift :
    NatTrans.CommShift (eqToIso (endomorphismDerivedHom_fac A D E hE)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A D) (moduleQuasiIso A D)
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
      (endomorphismDerivedHom A D E hE)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A D)
    (moduleQuasiIso A D) ℤ
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismDerivedHom A D E hE)

end
end SerrePositivity.DifferentialGraded
end

end DerivedShiftCoherence

/-! ## DerivedTriangleComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedTriangleComparison.lean） -/

/-! # 主K・主導来Hom比較のshift整合性と導来Homの三角性 -/

@[expose] public section DerivedTriangleComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

local instance : (endomorphismModuleHom A D E).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismModuleHom A D E).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE

lemma endomorphismModuleHomHomotopyFac_commShift :
    NatTrans.CommShift (eqToIso (endomorphismModuleHom A D E).onHomotopy_fac).hom ℤ := by
  have he : eqToIso (endomorphismModuleHom A D E).onHomotopy_fac =
      dgModuleFunctorHomotopyFacIso A D (EndomorphismObject E) (endomorphismModuleHom A D E) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rfl
  rw [he]
  exact dgModuleFunctorHomotopyFacIso_commShift A D (EndomorphismObject E)
    (endomorphismModuleHom A D E)

lemma endomorphismDerivedHomHomotopyIso_commShift :
    NatTrans.CommShift (endomorphismDerivedHomHomotopyIso A D E hE).hom ℤ := by
  let := endomorphismModuleHomHomotopyFac_commShift A D E
  let := endomorphismDerivedHomFac_commShift A D E hE
  unfold endomorphismDerivedHomHomotopyIso
  apply quotientNatIsoLift_commShift
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

/-- 実際の主導来Homは、全Hom写像から構成したshift構造について三角関手である。 -/
lemma endomorphismDerivedHomIsTriangulated :
    (endomorphismDerivedHom A D E hE).IsTriangulated := by
  let := dgModuleFunctorHomotopyIsTriangulated A D (EndomorphismObject E)
    (endomorphismModuleHom A D E)
  let := endomorphismDerivedHomHomotopyIso_commShift A D E hE
  exact Functor.isTriangulated_of_precomp_iso
    (endomorphismDerivedHomHomotopyIso A D E hE).symm

end SerrePositivity.DifferentialGraded
end

end DerivedTriangleComparison

/-! ## DerivedTensorTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedTensorTriangles.lean） -/

/-! # 実際の再構成導来tensorと随伴の整合的shift・三角性 -/

@[expose] public section DerivedTensorTriangles
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE
local instance : (endomorphismDerivedHom A D E hE).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E hE

/-- 導来随伴から実際の左関手へ運ぶ整合的shift。 -/
@[instance_reducible]
def endomorphismDerivedTensorCommShift : (endomorphismDerivedTensor A D E).CommShift ℤ :=
  (endomorphismDerivedAdjunction A D E hE).leftAdjointCommShift ℤ

lemma endomorphismDerivedAdjunction_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    (endomorphismDerivedAdjunction A D E hE).CommShift ℤ :=
  (endomorphismDerivedAdjunction A D E hE).commShift_of_rightAdjoint ℤ

lemma endomorphismDerivedUnit_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    NatTrans.CommShift (endomorphismDerivedUnit A D E hE) ℤ := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  unfold endomorphismDerivedUnit
  infer_instance

lemma endomorphismDerivedCounit_commShift :
    letI := endomorphismDerivedTensorCommShift A D E hE
    NatTrans.CommShift (endomorphismDerivedCounit A D E hE) ℤ := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  unfold endomorphismDerivedCounit
  infer_instance

lemma endomorphismDerivedTensorIsTriangulated :
    letI := endomorphismDerivedTensorCommShift A D E hE
    (endomorphismDerivedTensor A D E).IsTriangulated := by
  let := endomorphismDerivedTensorCommShift A D E hE
  let := endomorphismDerivedAdjunction_commShift A D E hE
  exact (endomorphismDerivedAdjunction A D E hE).isTriangulated_leftAdjoint

end SerrePositivity.DifferentialGraded
end

end DerivedTensorTriangles

/-! ## CompactGenerator（旧 SerrePositivity/DifferentialGraded/Endomorphism/CompactGenerator.lean） -/

/-! # 指定compact生成元の下での導来Homの保守性

compact性と全整数shiftによる零対象の検出を別の成分として明示する。
導来圏全体の同値をこの段階で結論しない。
-/

@[expose] public section CompactGenerator
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 指定対象自身のcompact性と、その整数shiftによる全導来対象の零性の検出。 -/
def endomorphismCompactGenerator : Prop :=
  moduleCompact A D ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ∧
    ∀ X : DerivedModuleCategory A D,
      (∀ n : ℤ, Subsingleton
        (((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ⟶ X⟦n⟧)) → IsZero X

variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE
local instance : (endomorphismDerivedHom A D E hE).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E hE

/-- compact生成仮定の検出成分と、正則End加群のtensor像の計算から零性を反映する。 -/
lemma endomorphismDerivedHom_reflectsZero (hCG : endomorphismCompactGenerator A D E)
    (X : DerivedModuleCategory A D) (hX : IsZero ((endomorphismDerivedHom A D E hE).obj X)) :
    IsZero X := by
  apply hCG.2 X
  intro n
  let R := endomorphismDerivedHom A D E hE
  let G := (moduleToDerived A (EndomorphismObject E)).obj
    (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))))
  have hz : IsZero (R.obj (X⟦n⟧)) :=
    ((shiftFunctor (DerivedModuleCategory A (EndomorphismObject E)) n).map_isZero hX).of_iso
      ((R.commShiftIso n).app X)
  let e := (Iso.homCongr (endomorphismDerivedTensor_regularIso A D E).symm
    (Iso.refl (X⟦n⟧))).trans ((endomorphismDerivedAdjunction A D E hE).homEquiv G (X⟦n⟧))
  exact ⟨fun f g => e.injective (hz.eq_of_tgt (e f) (e g))⟩

/-- 三角性と零性の反映から、実際の導来Homは同型を反映する。 -/
lemma endomorphismDerivedHom_reflectsIso (hCG : endomorphismCompactGenerator A D E)
    {X Y : DerivedModuleCategory A D} (f : X ⟶ Y)
    [IsIso ((endomorphismDerivedHom A D E hE).map f)] : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  let R := endomorphismDerivedHom A D E hE
  have hRT := R.map_distinguished T hT
  have hz : IsZero (R.obj Z) :=
    ((R.mapTriangle.obj T).isZero₃_iff_isIso₁ hRT).2 (by
      change IsIso ((endomorphismDerivedHom A D E hE).map f)
      infer_instance)
  exact (T.isZero₃_iff_isIso₁ hT).1
    (endomorphismDerivedHom_reflectsZero A D E hE hCG Z hz)

/-- 明示したcompact生成仮定の下でのみ使う保守性の型クラス。 -/
lemma endomorphismDerivedHomReflectsIsomorphisms
    (hCG : endomorphismCompactGenerator A D E) :
    (endomorphismDerivedHom A D E hE).ReflectsIsomorphisms where
  reflects f := endomorphismDerivedHom_reflectsIso A D E hE hCG f

end SerrePositivity.DifferentialGraded
end

end CompactGenerator

/-! ## EssentialImageRetracts（旧 SerrePositivity/DifferentialGraded/Endomorphism/EssentialImageRetracts.lean） -/

/-! # 再構成比較の本質的像のretract閉性と正則生成対象 -/

@[expose] public section EssentialImageRetracts
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

lemma fullyFaithfulEssImage_of_retract {C : Type v} {B : Type w} [Category* C] [Category* B]
    (F : C ⥤ B) [F.Full] [F.Faithful] [IsIdempotentComplete C]
    {X Y : B} (a : Retract X Y) (hY : F.essImage Y) : F.essImage X := by
  obtain ⟨M, ⟨e⟩⟩ := hY
  let b : Retract X (F.obj M) := a.trans (Retract.ofIso e.symm)
  let p := F.preimage (b.r ≫ b.i)
  have hpmap : F.map p = b.r ≫ b.i := F.map_preimage _
  have hp : p ≫ p = p := F.map_injective (by
    rw [F.map_comp, hpmap]
    simp only [Category.assoc, b.retract_assoc])
  obtain ⟨N, j, t, hjt, htj⟩ := IsIdempotentComplete.idempotents_split M p hp
  have hri : F.map t ≫ F.map j = b.r ≫ b.i := by rw [← F.map_comp, htj, hpmap]
  have hJT : F.map j ≫ F.map t = 𝟙 _ := by rw [← F.map_comp, hjt, F.map_id]
  refine ⟨N, ⟨{
    hom := F.map j ≫ b.r
    inv := b.i ≫ F.map t
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · calc
      (F.map j ≫ b.r) ≫ (b.i ≫ F.map t) = F.map j ≫ (b.r ≫ b.i) ≫ F.map t := by
        simp only [Category.assoc]
      _ = F.map j ≫ (F.map t ≫ F.map j) ≫ F.map t := by rw [hri]
      _ = (F.map j ≫ F.map t) ≫ (F.map j ≫ F.map t) := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hJT, Category.id_comp]
  · calc
      (b.i ≫ F.map t) ≫ (F.map j ≫ b.r) = b.i ≫ (F.map t ≫ F.map j) ≫ b.r := by
        simp only [Category.assoc]
      _ = b.i ≫ (b.r ≫ b.i) ≫ b.r := by rw [hri]
      _ = 𝟙 _ := by simp only [Category.assoc, b.retract_assoc, b.retract]

lemma fullyFaithfulEssImageStableUnderRetracts {C : Type v} {B : Type w}
    [Category* C] [Category* B] (F : C ⥤ B) [F.Full] [F.Faithful] [IsIdempotentComplete C] :
    F.essImage.IsStableUnderRetracts where
  of_retract a hY := fullyFaithfulEssImage_of_retract F a hY

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

/-- 主Perfから全主導来圏へ向かう導来Hom比較。 -/
def perfectEndomorphismHomToDerived :
    PerfectModuleCategoryOver A D S ⥤ DerivedModuleCategory A (EndomorphismObject E.val) :=
  perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1

lemma perfectEndomorphismHomToDerived_full
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).Full := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full := by
    unfold perfectModuleInclusion
    infer_instance
  change (perfectEndomorphismHomToPerfect A D S E hgen ⋙
    perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full
  infer_instance

lemma perfectEndomorphismHomToDerived_faithful
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).Faithful := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful := by
    unfold perfectModuleInclusion
    infer_instance
  change (perfectEndomorphismHomToPerfect A D S E hgen ⋙
    perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful
  infer_instance

lemma perfectEndomorphismEssentialImageStableUnderRetracts
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsStableUnderRetracts := by
  have := perfectEndomorphismHomToDerived_full A D S E hgen
  have := perfectEndomorphismHomToDerived_faithful A D S E hgen
  exact fullyFaithfulEssImageStableUnderRetracts _

lemma perfectEndomorphismEssentialImage_regular :
    (perfectEndomorphismHomToDerived A D S E).essImage
      ((moduleToDerived A (EndomorphismObject E.val)).obj
        (ForgetEnrichment.of (Complex A) (representable A (.point : EndomorphismObject E.val)))) :=
  ⟨⟨(moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E.val), E.property.2⟩,
    ⟨endomorphismDerivedHom_selfIso A D E.val E.property.1⟩⟩

end SerrePositivity.DifferentialGraded
end

end EssentialImageRetracts

/-! ## EssentialImageShift（旧 SerrePositivity/DifferentialGraded/Endomorphism/EssentialImageShift.lean） -/

/-! # 再構成比較の本質的像の整数shift閉性 -/

@[expose] public section EssentialImageShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismEssentialImage_shift
    {Y : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hY : (perfectEndomorphismHomToDerived A D S E).essImage Y) (s : ℤ) :
    (perfectEndomorphismHomToDerived A D S E).essImage (Y⟦s⟧) := by
  obtain ⟨X, ⟨e⟩⟩ := hY
  let M := X.obj.as.obj
  have hM : modulePerfectOver A D S ((moduleToDerived A D).obj M) := X.property
  let Xs : PerfectModuleCategoryOver A D S :=
    ⟨(moduleToDerived A D).obj (M⟦s⟧), (modulePerfectOver A D S).prop_of_iso
      (((moduleToDerived A D).commShiftIso s).app M).symm
      ((modulePerfectOver A D S).le_shift s _ hM)⟩
  refine ⟨Xs, ⟨?_⟩⟩
  exact endomorphismDerivedHomComputation A D E.val E.property.1 (M⟦s⟧) ≪≫
    (moduleToDerived A (EndomorphismObject E.val)).mapIso
      (dgModuleFunctorShiftIso A (EndomorphismObject E.val) D
        (endomorphismModuleHom A D E.val) s (ForgetEnrichment.to (Complex A) M)) ≪≫
    ((moduleToDerived A (EndomorphismObject E.val)).commShiftIso s).app
      ((endomorphismModuleHom A D E.val).onClosed.obj M) ≪≫
    (shiftFunctor (DerivedModuleCategory A (EndomorphismObject E.val)) s).mapIso
      ((endomorphismDerivedHomComputation A D E.val E.property.1 M).symm ≪≫ e)

instance perfectEndomorphismEssentialImageStableUnderShift :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ hY => perfectEndomorphismEssentialImage_shift A D S E hY s⟩

end SerrePositivity.DifferentialGraded
end

end EssentialImageShift

/-! ## EssentialImageTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/EssentialImageTriangles.lean） -/

/-! # 再構成比較の本質的像のdistinguished triangle閉性 -/

@[expose] public section EssentialImageTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma perfectEndomorphismEssentialImage_triangle_obj₃
    (T : Triangle (DerivedModuleCategory A (EndomorphismObject E.val)))
    (hT : T ∈ distTriang _)
    (h₁ : (perfectEndomorphismHomToDerived A D S E).essImage T.obj₁)
    (h₂ : (perfectEndomorphismHomToDerived A D S E).essImage T.obj₂) :
    (perfectEndomorphismHomToDerived A D S E).essImage T.obj₃ := by
  let G := perfectEndomorphismHomToDerived A D S E
  let R := endomorphismDerivedHom A D E.val E.property.1
  let Q := moduleToDerived A (EndomorphismObject E.val)
  have : G.Full := perfectEndomorphismHomToDerived_full A D S E hgen
  obtain ⟨X₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨q, hq⟩ := G.map_surjective (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  let P₁ := moduleCanonicalProjectiveResolution A D X₁.obj.as.obj
  let P₂ := moduleCanonicalProjectiveResolution A D X₂.obj.as.obj
  let c₁ : (moduleToDerived A D).obj P₁.obj ≅ X₁.obj := moduleDerivedIso A D P₁.π P₁.quasiIso
  let c₂ : (moduleToDerived A D).obj P₂.obj ≅ X₂.obj := moduleDerivedIso A D P₂.π P₂.quasiIso
  obtain ⟨f, hf⟩ := moduleProjectiveToDerived_map_surjective A D P₁.projective
    (c₁.hom ≫ q.hom ≫ c₂.inv)
  let r₁ := (endomorphismDerivedHomComputation A D E.val E.property.1 P₁.obj).symm ≪≫ R.mapIso c₁
  let r₂ := (endomorphismDerivedHomComputation A D E.val E.property.1 P₂.obj).symm ≪≫ R.mapIso c₂
  have hfac : (moduleToDerived A D).map f ≫ c₂.hom = c₁.hom ≫ q.hom := by
    rw [hf]
    simp only [Category.assoc, c₂.inv_hom_id, Category.comp_id]
  have hmap := congrArg R.map hfac
  simp only [CategoryTheory.Functor.map_comp] at hmap
  have hr : Q.map ((endomorphismModuleHom A D E.val).onClosed.map f) ≫ r₂.hom =
      r₁.hom ≫ R.map q.hom := by
    have hn := congrArg (fun k => k ≫ R.map c₂.hom)
      (endomorphismDerivedHomComputation_inv_naturality A D E.val E.property.1 f)
    have hc := congrArg (fun k =>
      (endomorphismDerivedHomComputation A D E.val E.property.1 P₁.obj).inv ≫ k) hmap
    simp only [Category.assoc] at hn hc
    exact (hn.trans hc).trans (Category.assoc _ _ _).symm
  have hq' : R.map q.hom = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hq
  let he : Arrow.mk (moduleDerivedConeTriangle A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk (r₁ ≪≫ e₁) (r₂ ≪≫ e₂) (by
      change (r₁.hom ≫ e₁.hom) ≫ T.mor₁ =
        Q.map ((endomorphismModuleHom A D E.val).onClosed.map f) ≫ (r₂.hom ≫ e₂.hom)
      rw [← Category.assoc _ r₂.hom e₂.hom, hr, hq']
      simp only [Category.assoc, e₂.inv_hom_id, Category.comp_id])
  obtain ⟨et, _⟩ := exists_iso_of_arrow_iso
    (moduleDerivedConeTriangle A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)) T
    (moduleDerivedConeTriangle_distinguished A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)) hT he
  have hp₁ := (modulePerfectOver A D S).prop_of_iso c₁.symm X₁.property
  have hp₂ := (modulePerfectOver A D S).prop_of_iso c₂.symm X₂.property
  have hcone := (modulePerfectOver A D S).ext_of_isTriangulatedClosed₃'
    (moduleDerivedConeTriangle A D f) (moduleDerivedConeTriangle_distinguished A D f) hp₁ hp₂
  rw [ObjectProperty.isoClosure_eq_self] at hcone
  refine ⟨⟨(moduleToDerived A D).obj (moduleCone A D f), hcone⟩, ⟨?_⟩⟩
  exact ((Q.mapIso (dgModuleFunctorConeIso A D (EndomorphismObject E.val)
      (endomorphismModuleHom A D E.val) f)) ≪≫
    (endomorphismDerivedHomComputation A D E.val E.property.1 (moduleCone A D f)).symm).symm ≪≫
      Triangle.π₃.mapIso et

lemma perfectEndomorphismEssentialImageTriangulatedClosed₃ :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (perfectEndomorphismEssentialImage_triangle_obj₃ A D S E hgen)

lemma perfectEndomorphismEssentialImageTriangulatedClosed₂ :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulatedClosed₂ := by
  have := perfectEndomorphismEssentialImageTriangulatedClosed₃ A D S E hgen
  exact ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

end SerrePositivity.DifferentialGraded
end

end EssentialImageTriangles

/-! ## PerfectEquivalence（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectEquivalence.lean） -/

/-! # thick生成による主Perf同値とenhancement比較の本質的全射

全Hom擬同型とは別に、正則生成対象・三角閉性・retract閉性から本質的全射を証明する。
-/

@[expose] public section PerfectEquivalence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma perfectEndomorphismEssentialImageIsTriangulated :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulated := by
  let P := (perfectEndomorphismHomToDerived A D S E).essImage
  have : P.IsTriangulatedClosed₂ :=
    perfectEndomorphismEssentialImageTriangulatedClosed₂ A D S E hgen
  have : P.IsStableUnderRetracts :=
    perfectEndomorphismEssentialImageStableUnderRetracts A D S E hgen
  have : P.Nonempty := ObjectProperty.nonempty_of_prop
    (perfectEndomorphismEssentialImage_regular A D S E)
  have : P.ContainsZero := inferInstance
  exact ⟨⟩

lemma perfectEndomorphismEssentialImage_containsPerfect :
    modulePerfect A (EndomorphismObject E.val) ≤
      (perfectEndomorphismHomToDerived A D S E).essImage := by
  have := perfectEndomorphismEssentialImageIsTriangulated A D S E hgen
  have := perfectEndomorphismEssentialImageStableUnderRetracts A D S E hgen
  apply (modulePerfect_le_iff_generators A (EndomorphismObject E.val)
    (perfectEndomorphismHomToDerived A D S E).essImage).2
  intro b
  cases b
  exact perfectEndomorphismEssentialImage_regular A D S E

instance perfectEndomorphismHomToPerfectEssSurj :
    (perfectEndomorphismHomToPerfect A D S E hgen).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := perfectEndomorphismEssentialImage_containsPerfect A D S E hgen
      Y.obj Y.property
    exact ⟨X, ⟨(modulePerfect A (EndomorphismObject E.val)).isoMk e⟩⟩

instance perfectEndomorphismHomToPerfectIsEquivalence :
    (perfectEndomorphismHomToPerfect A D S E hgen).IsEquivalence where

/-- 主導来Homの実際の制限を順関手とする、主Perf間の同値。 -/
def perfectEndomorphismEquivalence :
    PerfectModuleCategoryOver A D S ≌ PerfectModuleCategory A (EndomorphismObject E.val) :=
  (perfectEndomorphismHomToPerfect A D S E hgen).asEquivalence

/-- U13のenhancement間のdg関手は、H⁰で本質的全射。 -/
instance perfectEndomorphismDGHomotopyEssSurj :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.EssSurj where
  mem_essImage Y := by
    let F := (perfectEndomorphismDG A D S E hgen).onHomotopy
    let P := perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ
    have : (F ⋙ P).EssSurj := Functor.essSurj_of_iso
      (perfectEndomorphismDerivedComparison A D S E hgen).symm
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F ⋙ P) (P.obj Y)
    exact ⟨X, ⟨P.preimageIso e⟩⟩

/-- 全Hom擬同型とH⁰本質的全射を独立の証拠から組み合わせた準同値。 -/
lemma perfectEndomorphismDG_quasiEquivalence :
    QuasiEquivalence (perfectEndomorphismDG A D S E hgen) :=
  ⟨perfectEndomorphismDG_homQuasiIso A D S E hgen,
    perfectEndomorphismDGHomotopyEssSurj A D S E hgen⟩

end SerrePositivity.DifferentialGraded
end

end PerfectEquivalence

/-! ## PerfectShiftTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectShiftTriangles.lean） -/

/-! # 主Perf比較の整合的shift・三角性と包含図式 -/

@[expose] public section PerfectShiftTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

local instance : (endomorphismDerivedHom A D E.val E.property.1).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1
local instance : (endomorphismDerivedHom A D E.val E.property.1).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E.val E.property.1

/-- 既存の主Perf制限に、導来Homから制限した整合的shiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismHomCommShift :
    (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ := by
  unfold perfectEndomorphismHomToPerfect
  infer_instance

local instance : (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen

/-- 主Perf比較と主導来Homの包含正方形。 -/
def perfectEndomorphismHomInclusionIso :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1 :=
  (modulePerfect A (EndomorphismObject E.val)).liftCompιIso _ _

lemma perfectEndomorphismHomInclusionIso_commShift :
    NatTrans.CommShift (perfectEndomorphismHomInclusionIso A D S E hgen).hom ℤ := by
  unfold perfectEndomorphismHomInclusionIso
  infer_instance

lemma perfectEndomorphismHomIsTriangulated :
    (perfectEndomorphismHomToPerfect A D S E hgen).IsTriangulated := by
  unfold perfectEndomorphismHomToPerfect
  infer_instance

/-- 包含正方形を三角形の圏上の自然な正方形として保持する。 -/
def perfectEndomorphismHomTriangleSquareIso :
    (perfectEndomorphismHomToPerfect A D S E hgen).mapTriangle ⋙
        (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D S).mapTriangle ⋙
        (endomorphismDerivedHom A D E.val E.property.1).mapTriangle := by
  let := perfectEndomorphismHomInclusionIso_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismHomInclusionIso A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

local instance : (perfectEndomorphismEquivalence A D S E hgen).functor.CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen

/-- 主Perf同値の逆関手には、随伴から一意に定まる整合的shiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismEquivalenceInverseCommShift :
    (perfectEndomorphismEquivalence A D S E hgen).inverse.CommShift ℤ :=
  (perfectEndomorphismEquivalence A D S E hgen).commShiftInverse ℤ

local instance : (perfectEndomorphismEquivalence A D S E hgen).inverse.CommShift ℤ :=
  perfectEndomorphismEquivalenceInverseCommShift A D S E hgen

lemma perfectEndomorphismEquivalence_commShift :
    (perfectEndomorphismEquivalence A D S E hgen).CommShift ℤ :=
  (perfectEndomorphismEquivalence A D S E hgen).commShift_of_functor ℤ

/-- 順・逆両関手が三角的である主Perf同値。 -/
lemma perfectEndomorphismEquivalence_isTriangulated :
    letI := perfectEndomorphismEquivalence_commShift A D S E hgen
    (perfectEndomorphismEquivalence A D S E hgen).IsTriangulated := by
  let := perfectEndomorphismEquivalence_commShift A D S E hgen
  exact Equivalence.IsTriangulated.mk' _ (perfectEndomorphismHomIsTriangulated A D S E hgen)

end SerrePositivity.DifferentialGraded
end

end PerfectShiftTriangles

/-! ## PerfectTensor（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectTensor.lean） -/

/-! # 実際の再構成導来tensorの主Perfへの制限 -/

@[expose] public section PerfectTensor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

local instance : (endomorphismDerivedTensor A D E.val).CommShift ℤ :=
  endomorphismDerivedTensorCommShift A D E.val E.property.1
local instance : (endomorphismDerivedTensor A D E.val).IsTriangulated :=
  endomorphismDerivedTensorIsTriangulated A D E.val E.property.1

/-- 指定対象がperfectなら、再構成導来tensorは全perfect End加群をPerf_Sへ送る。 -/
lemma perfectEndomorphismTensor_obj_perfect
    {N : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hN : modulePerfect A (EndomorphismObject E.val) N) :
    modulePerfectOver A D S ((endomorphismDerivedTensor A D E.val).obj N) := by
  let P := (modulePerfectOver A D S).inverseImage (endomorphismDerivedTensor A D E.val)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun h hY => (modulePerfectOver A D S).prop_of_retract
      (h.map (endomorphismDerivedTensor A D E.val)) hY⟩
  apply ((modulePerfect_le_iff_generators A (EndomorphismObject E.val) P).2 ?_) N hN
  intro b
  cases b
  change modulePerfectOver A D S _
  exact (modulePerfectOver A D S).prop_of_iso
    (endomorphismDerivedTensor_regularIso A D E.val).symm E.property.2

/-- 既存の主導来tensorそのものを主Perfへ制限する。thick生成仮定は不要。 -/
def perfectEndomorphismTensorToPerfect :
    PerfectModuleCategory A (EndomorphismObject E.val) ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
      endomorphismDerivedTensor A D E.val)
    (fun N => perfectEndomorphismTensor_obj_perfect A D S E N.property)

@[instance_reducible]
def perfectEndomorphismTensorCommShift :
    (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ := by
  unfold perfectEndomorphismTensorToPerfect
  infer_instance

local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E

lemma perfectEndomorphismTensorIsTriangulated :
    (perfectEndomorphismTensorToPerfect A D S E).IsTriangulated := by
  unfold perfectEndomorphismTensorToPerfect
  infer_instance

def perfectEndomorphismTensorInclusionIso :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        endomorphismDerivedTensor A D E.val :=
  (modulePerfectOver A D S).liftCompιIso _ _

lemma perfectEndomorphismTensorInclusionIso_commShift :
    NatTrans.CommShift (perfectEndomorphismTensorInclusionIso A D S E).hom ℤ := by
  unfold perfectEndomorphismTensorInclusionIso
  infer_instance

end SerrePositivity.DifferentialGraded
end

end PerfectTensor

/-! ## PerfectTensorDG（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectTensorDG.lean） -/

/-! # U13の実際のdg enhancementへの再構成tensorの制限 -/

@[expose] public section PerfectTensorDG
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismTensorDG_obj_perfect (N : PerfectDGModule A (EndomorphismObject E.val)) :
    modulePerfectOver A D S ((moduleToDerived A D).obj
      ((endomorphismModuleTensor A D E.val).onClosed.obj
        (ForgetEnrichment.of (Complex A) N.val))) :=
  (modulePerfectOver A D S).prop_of_iso
    (endomorphismDerivedTensorProjectiveComputation A D E.val
      (ForgetEnrichment.of (Complex A) N.val) N.property.1)
    (perfectEndomorphismTensor_obj_perfect A D S E N.property.2)

/-- 対象は実際のunderived tensorであり、射影性とperfect性を証拠として保持する。 -/
def perfectEndomorphismTensorDG :
    DGFunctor A (PerfectDGModule A (EndomorphismObject E.val)) (PerfectDGModuleOver A D S) where
  obj N := ⟨(endomorphismModuleTensor A D E.val).obj N.val,
    endomorphismModuleTensor_homotopicallyProjective A D E.val E.property.1 N.property.1,
    perfectEndomorphismTensorDG_obj_perfect A D S E N⟩
  map N N' := (endomorphismModuleTensor A D E.val).map N.val N'.val
  map_id N := (endomorphismModuleTensor A D E.val).map_id N.val
  map_comp N N' N'' := (endomorphismModuleTensor A D E.val).map_comp N.val N'.val N''.val

lemma perfectEndomorphismTensorDG_inclusion_square :
    (perfectEndomorphismTensorDG A D S E).comp (perfectDGModuleInclusion A D S) =
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).comp
        (endomorphismModuleTensor A D E.val) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (perfectEndomorphismTensorDG A D S E).comp (perfectDGModuleInclusion A D S))
    (G := (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).comp
      (endomorphismModuleTensor A D E.val)) (fun _ => rfl)
  intro N N'
  simp only [eqToHom_refl, Category.comp_id]
  exact (Category.id_comp _).symm

end SerrePositivity.DifferentialGraded
end

end PerfectTensorDG

/-! ## PerfectAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectAdjunction.lean） -/

/-! # 再構成導来随伴の主Perf制限と実際のtensor逆関手 -/

@[expose] public section PerfectAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- 全導来圏での実際のtensor–Hom随伴を、完全忠実な包含に沿って制限する。 -/
def perfectEndomorphismAdjunction :
    perfectEndomorphismTensorToPerfect A D S E ⊣
      perfectEndomorphismHomToPerfect A D S E hgen :=
  (endomorphismDerivedAdjunction A D E.val E.property.1).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (modulePerfect A (EndomorphismObject E.val)).ι)
    (Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι)
    (perfectEndomorphismTensorInclusionIso A D S E).symm
    (perfectEndomorphismHomInclusionIso A D S E hgen).symm

lemma perfectEndomorphismUnit_inclusion
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).map
        ((perfectEndomorphismAdjunction A D S E hgen).unit.app N) =
      (endomorphismDerivedUnit A D E.val E.property.1).app N.obj := by
  unfold perfectEndomorphismAdjunction
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  change (endomorphismDerivedAdjunction A D E.val E.property.1).unit.app N.obj ≫
    (endomorphismDerivedHom A D E.val E.property.1).map (𝟙 _) ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.comp_id _

lemma perfectEndomorphismCounit_inclusion (M : PerfectModuleCategoryOver A D S) :
    (perfectModuleInclusion A D S).map
        ((perfectEndomorphismAdjunction A D S E hgen).counit.app M) =
      (endomorphismDerivedCounit A D E.val E.property.1).app M.obj := by
  unfold perfectEndomorphismAdjunction
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  change 𝟙 _ ≫ (endomorphismDerivedTensor A D E.val).map (𝟙 _) ≫
    (endomorphismDerivedAdjunction A D E.val E.property.1).counit.app M.obj = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

lemma perfectEndomorphismUnit_isIso :
    IsIso (perfectEndomorphismAdjunction A D S E hgen).unit := by infer_instance

lemma perfectEndomorphismCounit_isIso :
    IsIso (perfectEndomorphismAdjunction A D S E hgen).counit := by infer_instance

include hgen in
lemma perfectEndomorphismTensor_isEquivalence :
    (perfectEndomorphismTensorToPerfect A D S E).IsEquivalence :=
  (perfectEndomorphismAdjunction A D S E hgen).isEquivalence_left_of_isEquivalence_right

/-- 既存の主Perf同値の逆は、実際の再構成導来tensorの制限と自然同型である。 -/
def perfectEndomorphismTensorInverseIso :
    perfectEndomorphismTensorToPerfect A D S E ≅
      (perfectEndomorphismEquivalence A D S E hgen).inverse :=
  (perfectEndomorphismAdjunction A D S E hgen).leftAdjointUniq
    (perfectEndomorphismEquivalence A D S E hgen).symm.toAdjunction

end SerrePositivity.DifferentialGraded
end

end PerfectAdjunction

/-! ## PerfectScalarTensor（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectScalarTensor.lean） -/

/-! # 実際のPerf tensor制限・U12d・導来係数変更の比較

非flat係数変更の計算条件は受入済みU12f APIと同じ証拠を明示して受け取る。
-/

@[expose] public section PerfectScalarTensor
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- Perf上の実際のtensorとU12d評価比較を、導来係数変更後の自然同型として保持する。 -/
def perfectEndomorphismTensorScalarEvaluationIso (d : D) :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ⋙
        moduleDerivedEvaluation A D d ⋙ ScalarExtension.complexDerivedExtension φ ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        moduleDerivedTensorRight A (EndomorphismObject E.val)
          ((endomorphismModuleAction A D E.val).leftAt d) ⋙
            ScalarExtension.complexDerivedExtension φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismTensorInclusionIso A D S E)
      (moduleDerivedEvaluation A D d ⋙ ScalarExtension.complexDerivedExtension φ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (endomorphismDerivedTensorEvaluationIso A D E.val d)
          (ScalarExtension.complexDerivedExtension φ) ≪≫ Functor.associator _ _ _)

lemma perfectEndomorphismTensorScalarEvaluationIso_app (d : D)
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    (perfectEndomorphismTensorScalarEvaluationIso φ D S E d).hom.app N =
      (ScalarExtension.complexDerivedExtension φ).map
        ((moduleDerivedEvaluation A D d).map
          ((perfectEndomorphismTensorInclusionIso A D S E).hom.app N)) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E.val d).hom.app N.obj) := by
  simp only [Functor.comp_obj, perfectEndomorphismTensorScalarEvaluationIso,
    Functor.isoWhiskerLeft_trans, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp]
  erw [Category.comp_id]
  rfl

/-- Perf対象の指定加群代表上で、実際のPerf tensorを非flat導来係数変更比較へ接続する。 -/
def perfectEndomorphismTensorBaseChange (d : D)
    {N : ModuleCategory A (EndomorphismObject E.val)}
    (hN : modulePerfect A (EndomorphismObject E.val) ((moduleToDerived A _).obj N))
    (P : ModuleProjectiveResolution A (EndomorphismObject E.val) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E.val)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E.val).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E.val))
      (ScalarExtension.rightModule φ (EndomorphismObject E.val)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (ScalarExtension.complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A D d).obj
          ((perfectModuleInclusion A D S).obj
            ((perfectEndomorphismTensorToPerfect A D S E).obj ⟨_, hN⟩))) ≅
      (moduleDerivedTensorRight A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E.val))
        (ScalarExtension.leftModule φ (EndomorphismObject E.val)
          ((endomorphismModuleAction A D E.val).leftAt d))).obj
        ((ScalarExtension.derivedExtension φ (EndomorphismObject E.val)).obj
          ((moduleToDerived A (EndomorphismObject E.val)).obj N)) :=
  (perfectEndomorphismTensorScalarEvaluationIso φ D S E d).app ⟨_, hN⟩ ≪≫
    ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E.val) P
      ((endomorphismModuleAction A D E.val).leftAt d) hPN hP'

end SerrePositivity.DifferentialGraded
end

end PerfectScalarTensor

/-! ## CompactUnitCounit（旧 SerrePositivity/DifferentialGraded/Endomorphism/CompactUnitCounit.lean） -/

/-! # Perf上の単位・余単位と、外部入力compact⇒Perfの利用

U13dは実装しない。compact⇒Perfを使う場合は明示した入力として受け取る。
-/

@[expose] public section CompactUnitCounit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma endomorphismDerivedUnit_isIso_onPerfect
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N.obj) := by
  have := perfectEndomorphismUnit_isIso A D S E hgen
  rw [← perfectEndomorphismUnit_inclusion A D S E hgen N]
  infer_instance

lemma endomorphismDerivedCounit_isIso_onPerfect (M : PerfectModuleCategoryOver A D S) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app M.obj) := by
  have := perfectEndomorphismCounit_isIso A D S E hgen
  rw [← perfectEndomorphismCounit_inclusion A D S E hgen M]
  infer_instance

/-- End側のcompact⇒Perfは外部から受け取る証拠として明示する。 -/
lemma endomorphismDerivedUnit_isIso_of_compact
    (compactToPerfect : ∀ N : DerivedModuleCategory A (EndomorphismObject E.val),
      moduleCompact A (EndomorphismObject E.val) N →
        modulePerfect A (EndomorphismObject E.val) N)
    (N : DerivedModuleCategory A (EndomorphismObject E.val))
    (hN : moduleCompact A (EndomorphismObject E.val) N) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_onPerfect A D S E hgen ⟨N, compactToPerfect N hN⟩

/-- 指定Sに対するcompact⇒Perf_Sも、自動推論せず外部の証拠として受け取る。 -/
lemma endomorphismDerivedCounit_isIso_of_compact
    (compactToPerfect : ∀ M : DerivedModuleCategory A D,
      moduleCompact A D M → modulePerfectOver A D S M)
    (M : DerivedModuleCategory A D) (hM : moduleCompact A D M) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app M) :=
  endomorphismDerivedCounit_isIso_onPerfect A D S E hgen ⟨M, compactToPerfect M hM⟩

end SerrePositivity.DifferentialGraded
end

end CompactUnitCounit
