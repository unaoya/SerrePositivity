module

public import SerrePositivity.Asymptotic.FreeSequence
public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Pi.Basic
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.StdBasis
public import SerrePositivity.PerfectComplex.Free.Support
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # 自由列の複体・ホモトピー圏・導来圏

## 概要

各段の鎖写像・ホモトピーを列全体のものに組み戻し、自由列の有界ホモトピー圏とその加法的 Karoubi 包絡を定める。共通有界な自由列の各段は K 射影的なので、ホモトピー圏から加群の導来圏の積への関手は完全忠実である。行列による係数変更とテンソル積の比較も与える。

## 方針

射やホモトピーに有界性を課さないので、各段で選んだデータをそのまま使える。

## 規約

Karoubi 包絡の三角構造やランクによる商はこの上の層で扱う。

## 使われ方

`RankQuotient` 以下。
-/

@[expose] public noncomputable section

universe u

section SequenceComplexPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の複体から第 `n` 段の複体を取り出す関手。 -/
def evaluateComplex (n : ℕ) :
    CochainComplex (FreeSequence R s) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)

instance (n : ℕ) : (evaluateComplex (R := R) (s := s) n).Additive :=
  inferInstanceAs ((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Additive

/-- 各段の鎖写像を自由列の鎖写像に組み戻す。 -/
def assembleChainMap {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f : ∀ n, (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj Q) : P ⟶ Q where
  f i n := ((f n).f i).hom
  comm' i j _ := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((f n).comm i j)

/-- 組み戻した鎖写像の第 `n` 段は元の鎖写像である。 -/
@[simp] lemma evaluate_assembleChainMap {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f : ∀ n, (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj Q) (n : ℕ) :
    (evaluateComplex n).map (assembleChainMap f) = f n := by
  ext i
  rfl

/-- 各段の鎖同型を、自由列の複体の鎖同型に組み戻す。 -/
def assembleComplexIso {P Q : CochainComplex (FreeSequence R s) ℤ}
    (e : ∀ n, (evaluateComplex n).obj P ≅ (evaluateComplex n).obj Q) : P ≅ Q where
  hom := assembleChainMap (fun n ↦ (e n).hom)
  inv := assembleChainMap (fun n ↦ (e n).inv)
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext i n
    exact congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) (e n).hom_inv_id)
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext i n
    exact congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) (e n).inv_hom_id)

/-- 各段のホモトピーを、自由列の複体間のホモトピーに組み戻す。 -/
def assembleHomotopy {P Q : CochainComplex (FreeSequence R s) ℤ} {f g : P ⟶ Q}
    (h : ∀ n, Homotopy ((evaluateComplex n).map f) ((evaluateComplex n).map g)) :
    Homotopy f g where
  hom i j n := ((h n).hom i j).hom
  zero i j hij := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((h n).zero i j hij)
  comm i := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((h n).comm i)

/-- 列全体でホモトピックであることは、各段でのホモトピーの存在と同値である。 -/
lemma nonempty_homotopy_iff {P Q : CochainComplex (FreeSequence R s) ℤ} (f g : P ⟶ Q) :
    Nonempty (Homotopy f g) ↔
      ∀ n, Nonempty (Homotopy ((evaluateComplex n).map f) ((evaluateComplex n).map g)) := by
  constructor
  · rintro ⟨h⟩ n
    exact ⟨(FreeSequence.evaluation n).mapHomotopy h⟩
  · intro h
    exact ⟨assembleHomotopy (fun n ↦ Classical.choice (h n))⟩

/-- ホモトピー圏の射の等式は、各段のホモトピー圏で判定できる。 -/
lemma quotient_map_eq_iff_pointwise {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f g : P ⟶ Q) :
    (HomotopyCategory.quotient _ _).map f = (HomotopyCategory.quotient _ _).map g ↔
      ∀ n, (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map f) =
        (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map g) := by
  constructor
  · intro h n
    exact HomotopyCategory.eq_of_homotopy _ _
      ((FreeSequence.evaluation n).mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h))
  · intro h
    exact HomotopyCategory.eq_of_homotopy _ _
      (assembleHomotopy (fun n ↦ HomotopyCategory.homotopyOfEq _ _ (h n)))

/-- `E_R` 上の共通有界ホモトピー圏。 -/
abbrev SequenceHomotopy (R : Type u) [CommRing R] (s : ℕ → ℕ) :=
  BoundedHomotopy (FreeSequence R s)

/-- 論文の `D_R` の加法圏としてのモデル。三角構造の延長は別の課題である。 -/
abbrev SequenceKaroubi (R : Type u) [CommRing R] (s : ℕ → ℕ) :=
  Idempotents.Karoubi (SequenceHomotopy R s)

/-- 列のホモトピー圏から、各段のホモトピー圏の積への関手。 -/
def pointwiseHomotopy : HomotopyCategory (FreeSequence R s) (.up ℤ) ⥤
    (ℕ → HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) where
  obj P n := ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).obj P
  map f n := ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map f
  map_id P := funext fun _ ↦ CategoryTheory.Functor.map_id _ P
  map_comp f g := funext fun _ ↦ CategoryTheory.Functor.map_comp _ f g

/-- ホモトピーの段ごとの組み戻しにより、積への関手は忠実である。 -/
instance : (pointwiseHomotopy (R := R) (s := s)).Faithful where
  map_injective {P Q} f g h := by
    have hf := HomotopyCategory.quotient_map_out f
    have hg := HomotopyCategory.quotient_map_out g
    rw [← hf, ← hg]
    apply (quotient_map_eq_iff_pointwise f.out g.out).2
    intro n
    change ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map f.out) =
      ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map g.out)
    rw [HomotopyCategory.quotient_map_out, HomotopyCategory.quotient_map_out]
    exact congrFun h n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 各段で選んだ鎖写像を組み戻せるので、積への関手は充満である。 -/
instance : (pointwiseHomotopy (R := R) (s := s)).Full where
  map_surjective {P Q} f := by
    let g := assembleChainMap (P := P.as) (Q := Q.as) (fun n ↦ (f n).out)
    refine ⟨(HomotopyCategory.quotient _ _).map g, ?_⟩
    funext n
    change (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map g) = f n
    dsimp only [g]
    rw [evaluate_assembleChainMap, HomotopyCategory.quotient_map_out]

/-- 共通有界な代表の各段には同じ次数の上下界が使える。 -/
lemma evaluateComplex_uniform_bounds (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) :
    ∃ a b : ℤ, ∀ n,
      ((evaluateComplex n).obj P).IsStrictlyGE a ∧
      ((evaluateComplex n).obj P).IsStrictlyLE b := by
  obtain ⟨a, b, ha, hb⟩ := hP
  refine ⟨a, b, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (FreeSequence.evaluation n).map_isZero (P.isZero_of_isStrictlyGE a i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (FreeSequence.evaluation n).map_isZero (P.isZero_of_isStrictlyLE b i hi)

end SerrePositivity.Asymptotic

end SequenceComplexPart

section SequenceDerivedPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界な自由列の各段は K 射影的である。 -/
lemma evaluateComplex_isKProjective (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (n : ℕ) :
    ((evaluateComplex n).obj P).IsKProjective := by
  obtain ⟨a, b, h⟩ := evaluateComplex_uniform_bounds P hP
  have := (h n).2
  have (i : ℤ) : Projective (((evaluateComplex n).obj P).X i) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin ((P.X i).rank n)))
  exact CochainComplex.isKProjective_of_projective _ b

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- 共通有界な自由列を、各段の導来圏の対象の列に移す関手。 -/
def pointwiseDerived : SequenceHomotopy R s ⥤ (ℕ → DerivedCategory (ModuleCat.{u} R)) where
  obj P n := DerivedCategory.Qh.obj (pointwiseHomotopy.obj P.obj n)
  map f n := DerivedCategory.Qh.map (pointwiseHomotopy.map f.hom n)
  map_id P := by funext n; simp
  map_comp f g := by funext n; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 導来圏の積への関手は忠実である。 -/
instance : (pointwiseDerived (R := R) (s := s)).Faithful where
  map_injective {P Q} f g h := by
    apply ObjectProperty.hom_ext
    apply pointwiseHomotopy.map_injective
    funext n
    have hb : strictlyBoundedComplex (FreeSequence R s) P.obj.as := by
      exact (boundedHomotopyProperty_quotient _ P.obj.as).1 P.property
    have := evaluateComplex_isKProjective P.obj.as hb n
    exact (CochainComplex.IsKProjective.Qh_map_bijective
      ((evaluateComplex n).obj P.obj.as) _).injective (congrFun h n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 導来圏の積への関手は充満である。 -/
instance : (pointwiseDerived (R := R) (s := s)).Full where
  map_surjective {P Q} f := by
    have hb : strictlyBoundedComplex (FreeSequence R s) P.obj.as := by
      exact (boundedHomotopyProperty_quotient _ P.obj.as).1 P.property
    have h (n : ℕ) : ∃ g : pointwiseHomotopy.obj P.obj n ⟶ pointwiseHomotopy.obj Q.obj n,
        DerivedCategory.Qh.map g = f n := by
      have := evaluateComplex_isKProjective P.obj.as hb n
      exact (CochainComplex.IsKProjective.Qh_map_bijective
        ((evaluateComplex n).obj P.obj.as) _).surjective (f n)
    choose g hg using h
    obtain ⟨k, hk⟩ := pointwiseHomotopy.map_surjective
      (show pointwiseHomotopy.obj P.obj ⟶ pointwiseHomotopy.obj Q.obj from g)
    refine ⟨ObjectProperty.homMk k, ?_⟩
    funext n
    change DerivedCategory.Qh.map (pointwiseHomotopy.map k n) = f n
    rw [hk]
    exact hg n

end SerrePositivity.Asymptotic

end SequenceDerivedPart

section FreeSequenceTensorPart

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory
open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}

/-- 行列への係数変更は、ベクトルの各係数への環準同型と両立する。 -/
lemma changeMatrix_apply_map (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : Fin a → R) :
    changeMatrix φ f (φ ∘ x) = φ ∘ f x := by
  funext j
  simp only [changeMatrix, Matrix.toLin'_apply, ← RingHom.map_mulVec,
    LinearMap.toMatrix'_mulVec, Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- 標準自由加群の係数変更をテンソル積として実現する同型。 -/
noncomputable def standardTensorIso (φ : R →+* S) (a : ℕ) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (Fin a → R)) ≅
      ModuleCat.of S (Fin a → S) := by
  letI := φ.toAlgebra
  exact (TensorProduct.piScalarRight R S S (Fin a)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- 標準自由加群のテンソル同型の自然性。 -/
lemma standardTensorIso_naturality (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom f) ≫ (standardTensorIso φ b).hom =
      (standardTensorIso φ a).hom ≫ ModuleCat.ofHom (changeMatrix φ f) := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (TensorProduct.piScalarRight R S S (Fin b)) (1 ⊗ₜ[R] f x) =
    changeMatrix φ f ((TensorProduct.piScalarRight R S S (Fin a)) (1 ⊗ₜ[R] x))
  simpa only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one, Function.comp_def] using
    (changeMatrix_apply_map φ f x).symm

/-- 自由列を評価してからテンソル積をとる操作と、行列の係数変更後の評価との自然同型。 -/
noncomputable def evaluationTensorIso (φ : R →+* S) (n : ℕ) :
    evaluation (R := R) (s := s) n ⋙ ModuleCat.extendScalars φ ≅
      changeRing φ ⋙ evaluation n :=
  NatIso.ofComponents (fun X ↦ standardTensorIso φ (X.rank n))
    (fun f ↦ standardTensorIso_naturality φ (f n))

/-- 自由列の複体の係数変更は、各段で実際のテンソル積複体と同型である。 -/
noncomputable def evaluateComplexTensorIso (φ : R →+* S) (n : ℕ)
    (K : CochainComplex (FreeSequence R s) ℤ) :
    baseChange φ ((evaluateComplex n).obj K) ≅
      (evaluateComplex n).obj (((changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K ≪≫
    (NatIso.mapHomologicalComplex (evaluationTensorIso φ n) (.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K).symm

end SerrePositivity.Asymptotic.FreeSequence

end FreeSequenceTensorPart
