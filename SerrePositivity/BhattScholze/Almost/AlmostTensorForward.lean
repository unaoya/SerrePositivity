module

public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.BhattScholze.Almost.AlmostTensor
public import SerrePositivity.HomologicalAlgebra.CochainTensorScalarCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology

/-! # 非有界複体の almost 零性と連結性

## 概要
BS 著者版 Proposition 10.4 の複体の同値と Lemma 10.5 の連結性の判定。

## 方針
上への切り捨ての差を一つのコホモロジー加群として扱い、固定した核の射影分解を
テンソルする。非有界の複体へは、各冪の Koszul 簡約で逐次余極限を取って移す。

## 規約
完備テンソルには元の半自由代表を使う。コホモロジー次数の零以下を連結とする。

## 使われ方
BS 著者版 Theorem 10.9 と Theorem 10.11 の almost 連結性の議論。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits HomologicalComplex DifferentialGraded
open CategoryTheory.Pretriangulated MonoidalCategory
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 上への切り捨ての包含を、元の複体への写像の自然性から作る。 -/
private def goodTruncationMap (X : Complex R) (m n : ℤ) (h : m ≤ n) :
    X.truncLE m ⟶ X.truncLE n := by
  have := (X.truncLE m).isStrictlyLE_of_le m n h
  exact inv ((X.truncLE m).ιTruncLE n) ≫ CochainComplex.truncLEMap (X.ιTruncLE m) n

@[reassoc] private lemma goodTruncationMap_inclusion
    (X : Complex R) (m n : ℤ) (h : m ≤ n) :
    goodTruncationMap X m n h ≫ X.ιTruncLE n = X.ιTruncLE m := by
  unfold goodTruncationMap
  simp only [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

private def goodTruncationSequence (X : Complex R) : ℕ ⥤ Complex R where
  obj n := X.truncLE (n : ℤ)
  map {m n} f := goodTruncationMap X m n (by exact_mod_cast leOfHom f)
  map_id n := by
    have : Mono (X.ιTruncLE (n : ℤ)) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE X
        (ComplexShape.embeddingUpIntLE (n : ℤ))))
    change goodTruncationMap X (n : ℤ) (n : ℤ) le_rfl = 𝟙 _
    apply (cancel_mono (X.ιTruncLE (n : ℤ))).mp
    rw [goodTruncationMap_inclusion, Category.id_comp]
  map_comp {m n k} f g := by
    have : Mono (X.ιTruncLE (k : ℤ)) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE X
        (ComplexShape.embeddingUpIntLE (k : ℤ))))
    have hmn : (m : ℤ) ≤ n := by exact_mod_cast leOfHom f
    have hnk : (n : ℤ) ≤ k := by exact_mod_cast leOfHom g
    change goodTruncationMap X m k (hmn.trans hnk) =
      goodTruncationMap X m n hmn ≫ goodTruncationMap X n k hnk
    apply (cancel_mono (X.ιTruncLE (k : ℤ))).mp
    simp only [Category.assoc, goodTruncationMap_inclusion]

private def goodTruncationCocone (X : Complex R) : Cocone (goodTruncationSequence X) where
  pt := X
  ι :=
    { app := fun n ↦ X.ιTruncLE n
      naturality := by
        intro m n f
        have hmn : (m : ℤ) ≤ n := by exact_mod_cast leOfHom f
        change goodTruncationMap X m n hmn ≫ X.ιTruncLE n = X.ιTruncLE m ≫ 𝟙 X
        rw [goodTruncationMap_inclusion, Category.comp_id] }

private theorem isIso_goodTruncationInclusion_f (X : Complex R) (n i : ℤ) (hi : i < n) :
    IsIso ((X.ιTruncLE n).f i) := by
  let e := (ComplexShape.embeddingUpIntLE n).op
  let j := (n - i).natAbs
  have hj : e.f j = i := by
    change n - ((n - i).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hnb : ¬ e.BoundaryGE j := by
    change ¬ (ComplexShape.embeddingUpIntLE n).BoundaryLE j
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    omega
  have hiso : IsIso ((X.op.πTruncGE e).f i) := by
    rw [HomologicalComplex.πTruncGE, e.isIso_liftExtend_f_iff _ _ hj]
    exact X.op.isIso_restrictionToTruncGE' e j hnb
  change IsIso (((X.op.πTruncGE e).f i).unop)
  infer_instance

/-- 各次数で包含がやがて同型になるので、元の複体が余極限となる。 -/
private def goodTruncationIsColimit (X : Complex R) :
    IsColimit (goodTruncationCocone X) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  let ev := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i
  let F := goodTruncationSequence X ⋙ ev
  let c : Cocone F := ev.mapCocone (goodTruncationCocone X)
  let N := i.toNat + 1
  have hi : i < (N : ℤ) := by dsimp [N]; omega
  have : IsIso (c.ι.app N) := isIso_goodTruncationInclusion_f X _ _ hi
  have hF : F.IsEventuallyConstantFrom N := by
    intro j f
    have hj : i < (j : ℤ) := by have := leOfHom f; omega
    have : IsIso (c.ι.app j) := isIso_goodTruncationInclusion_f X _ _ hj
    have : IsIso (F.map f ≫ c.ι.app j) := by rw [c.w f]; infer_instance
    exact IsIso.of_isIso_comp_right (F.map f) (c.ι.app j)
  exact hF.isColimitOfIsIso c


open CochainComplex

/-- 隣接する二つの切り捨ての差は、追加した次数のコホモロジー加群。 -/
private def goodTruncationLayerIso (X : Complex R) (n : ℤ) :
    DerivedCategory.Q.obj (mappingCone (goodTruncationMap X (n - 1) n (by omega))) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) n).obj (X.homology n) := by
  let f := goodTruncationMap X (n - 1) n (by omega)
  let T := (DerivedCategory.Q : Complex R ⥤ _).mapTriangle.obj (mappingCone.triangle f)
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
  let H (i : ℤ) := DerivedCategory.homologyFunctor (ModuleCat R) i
  have h₁ (i : ℤ) (hi : n - 1 < i) : IsZero ((H i).obj T.obj₁) := by
    have hle : T.obj₁.IsLE (n - 1) := by
      change (DerivedCategory.Q.obj (X.truncLE (n - 1))).IsLE (n - 1)
      infer_instance
    exact (DerivedCategory.isLE_iff _ _).mp hle i hi
  have h₂ (i : ℤ) (hi : n < i) : IsZero ((H i).obj T.obj₂) := by
    have hle : T.obj₂.IsLE n := by
      change (DerivedCategory.Q.obj (X.truncLE n)).IsLE n
      infer_instance
    exact (DerivedCategory.isLE_iff _ _).mp hle i hi
  have hmap (i : ℤ) (hi : i ≤ n - 1) : IsIso ((H i).map T.mor₁) := by
    have hf : QuasiIsoAt f i := by
      have := X.quasiIsoAt_ιTruncLE n i (by omega)
      have hc : QuasiIsoAt (f ≫ X.ιTruncLE n) i := by
        dsimp only [f]
        rw [goodTruncationMap_inclusion]
        exact X.quasiIsoAt_ιTruncLE (n - 1) i hi
      exact quasiIsoAt_of_comp_right f (X.ιTruncLE n) i
    change IsIso ((H i).map (DerivedCategory.Q.map f))
    exact (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) i) f).mpr
      ((quasiIsoAt_iff_isIso_homologyMap f i).mp hf)
  have hδ (i : ℤ) :
      DerivedCategory.HomologySequence.δ T i (i + 1) = 0 := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).mp
    by_cases hi : i + 1 ≤ n - 1
    · have := hmap (i + 1) hi
      infer_instance
    · exact (h₁ (i + 1) (by omega)).mono _
  have hzero (i : ℤ) (hi : i ≠ n) : IsZero ((H i).obj T.obj₃) := by
    have he : Epi ((H i).map T.mor₂) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)).mpr (hδ i)
    have hz : (H i).map T.mor₂ = 0 := by
      by_cases hii : i ≤ n - 1
      · have := hmap i hii
        exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mp inferInstance
      · exact (h₂ i (by omega)).eq_of_src _ _
    exact (IsZero.iff_id_eq_zero _).mpr ((cancel_epi ((H i).map T.mor₂)).mp (by rw [hz]; simp))
  have hge : T.obj₃.IsGE n :=
    (DerivedCategory.isGE_iff _ _).mpr (fun i hi ↦ hzero i (by omega))
  have hle : T.obj₃.IsLE n :=
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi ↦ hzero i (by omega))
  have he : Epi ((H n).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1)).mpr (hδ n)
  have hm : Mono ((H n).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT n).mpr
      ((h₁ n (by omega)).eq_of_src _ _)
  have : IsIso ((H n).map T.mor₂) := isIso_of_mono_of_epi _
  let eH : (H n).obj T.obj₃ ≅ X.homology n :=
    (asIso ((H n).map T.mor₂)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app (X.truncLE n) ≪≫
      (by
        have : IsIso ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map
            (X.ιTruncLE n)) := (quasiIsoAt_iff_isIso_homologyMap _ _).mp
          (X.quasiIsoAt_ιTruncLE n n le_rfl)
        exact asIso ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).map
          (X.ιTruncLE n)))
  exact normalizedPureHomologyIso T.obj₃ n ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) n).mapIso eH



open DerivedCompletion InfinityCategories

private theorem tensorRight_invertsQuasiIso (P : Complex R) (hP : complexKFlat R P) :
    (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).IsInvertedBy
      (tensorRight P ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (complexKFlat_quasiIso_left R hP f)

private def derivedTensorRight (P : Complex R) (hP : complexKFlat R P) :
    ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R :=
  Localization.lift (tensorRight P ⋙ DerivedCategory.Q) (tensorRight_invertsQuasiIso P hP)
    DerivedCategory.Q

private def derivedTensorRightIso (P : Complex R) (hP : complexKFlat R P) (X : Complex R) :
    (derivedTensorRight P hP).obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj (cochainTensor X P) :=
  (Localization.fac (tensorRight P ⋙ DerivedCategory.Q)
    (tensorRight_invertsQuasiIso P hP) DerivedCategory.Q).app X

private abbrev completedTensorRight (a : R) (P X : Complex R) : ConcreteDerivedCategory R :=
  (derivedComplexCompletionFunctor R a).obj (DerivedCategory.Q.obj (cochainTensor X P))

private theorem completedTensorRight_isZero_of_single (a : R) (P : Complex R)
    (hP : complexKFlat R P) (X : Complex R) (n : ℤ) (N : ModuleCat.{u} R)
    (iso : DerivedCategory.Q.obj X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj N)
    (hz : IsZero (completedTensorRight a P (cochainSingleZero N))) :
    IsZero (completedTensorRight a P X) := by
  let T := derivedTensorRight P hP
  let F := derivedComplexCompletionFunctor R a
  let C := CochainComplex.singleFunctors (ModuleCat R)
  let e : (CochainComplex.singleFunctor (ModuleCat R) n).obj N ≅
      (cochainSingleZero N)⟦(-n : ℤ)⟧ :=
    ((C.shiftIso (-n) n 0 (by omega)).app N).symm
  let ec := (derivedTensorRightIso P hP X).symm ≪≫
    T.mapIso iso ≪≫ derivedTensorRightIso P hP _
  let ez := (CategoryTheory.shiftFunctor (ConcreteDerivedCategory R) (-n)).map_isZero hz
  refine ez.of_iso (F.mapIso ec ≪≫ ?_)
  exact F.mapIso (DerivedCategory.Q.mapIso
      ((tensorRight P).mapIso e ≪≫ cochainTensorShiftLeft (cochainSingleZero N) P (-n)) ≪≫
    (DerivedCategory.Q.commShiftIso (-n)).app (cochainTensor (cochainSingleZero N) P)) ≪≫
    (F.commShiftIso (-n)).app _

private theorem completedTensorRight_truncation_step (a : R) (P X : Complex R)
    (hP : complexKFlat R P) (n : ℤ)
    (hN : IsZero (completedTensorRight a P (cochainSingleZero (X.homology n)))) :
    Nonempty (completedTensorRight a P (X.truncLE (n - 1)) ≅
      completedTensorRight a P (X.truncLE n)) := by
  let f := goodTruncationMap X (n - 1) n (by omega)
  let F := derivedComplexCompletionFunctor R a
  let T := F.mapTriangle.obj
    ((DerivedCategory.Q : Complex R ⥤ _).mapTriangle.obj
      (mappingCone.triangle (cochainTensorMap f (𝟙 P))))
  have hT : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished (cochainTensorMap f (𝟙 P)))
  have hz := completedTensorRight_isZero_of_single a P hP _ n _
    (goodTruncationLayerIso X n) hN
  have h₃ : IsZero T.obj₃ :=
    hz.of_iso (F.mapIso (DerivedCategory.Q.mapIso (cochainTensorConeLeft f P))).symm
  have := (T.isZero₃_iff_isIso₁ hT).mp h₃
  exact ⟨asIso T.mor₁⟩

/-- 各次数で、十分低い上界から有限回だけ切り捨ての上界を上げる。 -/
private theorem completedTensorRight_truncations_are_zero (a : R) (P X : Complex R)
    (hP : complexKFlat R P) (hP0 : P.IsStrictlyLE 0)
    (hN : ∀ n, IsZero (completedTensorRight a P (cochainSingleZero (X.homology n))))
    (n : ℤ) : IsZero (completedTensorRight a P (X.truncLE n)) := by
  let Y (j : ℤ) := completedTensorRight a P (X.truncLE j)
  have hle (j : ℤ) : (Y j).IsLE j := by
    have := cochainTensor_isStrictlyLE (X.truncLE j) P j 0
    have h : (DerivedCategory.Q.obj (cochainTensor (X.truncLE j) P)).IsLE (j + 0) :=
      inferInstance
    simpa only [add_zero] using derivedComplexCompletionFunctor_isLE R a _ _ h
  have hzero (i : ℤ) (j : ℤ) (hj : i - 1 ≤ j) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (Y j)) := by
    obtain ⟨k, hk⟩ := Int.le.dest hj
    rw [← hk]
    clear hk hj j
    induction k with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      exact (DerivedCategory.isLE_iff _ _).mp (hle (i - 1)) i (by omega)
    | succ k ih =>
      let j' := i - 1 + (↑(k + 1) : ℤ)
      obtain ⟨e⟩ := completedTensorRight_truncation_step a P X hP j' (hN j')
      have he : j' - 1 = i - 1 + (k : ℤ) := by dsimp [j']; omega
      rw [he] at e
      exact ih.of_iso ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e).symm
  have hh (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (Y n)) := by
    by_cases hi : i - 1 ≤ n
    · exact hzero i n hi
    · exact (DerivedCategory.isLE_iff _ _).mp (hle n) i (by omega)
  let f := (0 : Y n ⟶ 0)
  have : IsIso f := (DerivedCategory.isIso_iff (ModuleCat R) f).mpr (fun i ↦ by
    exact (hh i).isIso
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero (isZero_zero _)) _)
  exact (isZero_zero _).of_iso (asIso f)



private theorem isZero_Q_iff_acyclic (X : Complex R) :
    IsZero (DerivedCategory.Q.obj X) ↔ X.Acyclic := by
  constructor
  · intro hx i
    apply (exactAt_iff_isZero_homology X i).mpr
    exact ((DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero hx).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app X).symm
  · intro hx
    let f := (0 : X ⟶ 0)
    have h : QuasiIso f := by
      constructor
      intro i
      apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      exact (hx i).isZero_homology.isIso
        ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) i).map_isZero
          (isZero_zero _)) _
    have := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) f).mpr h
    exact (DerivedCategory.Q.map_isZero (isZero_zero _)).of_iso (asIso (DerivedCategory.Q.map f))

private theorem isZero_Q_scalarCone_of_isZero (a : R) (X : Complex R)
    (hx : IsZero (DerivedCategory.Q.obj X)) :
    IsZero (DerivedCategory.Q.obj ((scalarConeFunctor a).obj X)) := by
  let f := smulId a X
  let T := (DerivedCategory.Q : Complex R ⥤ _).mapTriangle.obj (mappingCone.triangle f)
  have hd : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
  have hi : IsIso T.mor₁ := hx.isIso hx _
  exact (T.isZero₃_iff_isIso₁ hd).mpr hi

/-- 完備化の前に Koszul 簡約を取り、完全な逐次余極限で消滅を移す。 -/
private theorem completedTensorRight_isZero_of_homology (a : R) (P X : Complex R)
    (hP : complexKFlat R P) (hP0 : P.IsStrictlyLE 0)
    (hN : ∀ n, IsZero (completedTensorRight a P (cochainSingleZero (X.homology n)))) :
    IsZero (completedTensorRight a P X) := by
  let Z := cochainTensor X P
  let F := derivedComplexCompletionFunctor R a
  have htrunc := completedTensorRight_truncations_are_zero a P X hP hP0 hN
  have hred (m : ℕ) : IsZero (DerivedCategory.Q.obj ((scalarConeFunctor (a ^ m)).obj Z)) := by
    let W := mappingCone (smulId (a ^ m) (cochainTensorUnit (R := R)))
    let G := tensorRight P ⋙ tensorLeft W
    let D := goodTruncationSequence X ⋙ G
    have hsmall : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE (ModuleCat.{u} R)
    have hacyc (n : ℕ) : (D.obj n).Acyclic := by
      let Y := cochainTensor (X.truncLE n) P
      have hc : IsZero (DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj Y)) :=
        (htrunc n).of_iso ((derivedComplexCompletionComparison R a).app Y).symm
      have hC := isZero_Q_scalarCone_of_isZero (a ^ m) _ hc
      have hY := hC.of_iso (complexCompletionReductionIso R a Y m)
      apply (isZero_Q_iff_acyclic _).mp
      exact hY.of_iso (DerivedCategory.Q.mapIso (cochainTensorUnitScalarConeIso (a ^ m) Y))
    have hc : (colimit D).Acyclic := complex_colimit_acyclic R D hacyc
    let e := (colimit.isColimit D).coconePointUniqueUpToIso
      (isColimitOfPreserves G (goodTruncationIsColimit X))
    exact ((isZero_Q_iff_acyclic _).mpr hc).of_iso
      (DerivedCategory.Q.mapIso (e ≪≫ cochainTensorUnitScalarConeIso (a ^ m) Z)).symm
  let f := (0 : Z ⟶ 0)
  have hf (m : ℕ) : QuasiIso ((scalarConeFunctor (a ^ m)).map f) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    exact (hred m).isIso
      (isZero_Q_scalarCone_of_isZero _ _ (DerivedCategory.Q.map_isZero (isZero_zero _))) _
  have hq := complexCompletionFunctor_map_quasiIso_of_koszul R a f hf
  have hF : IsIso (F.map (DerivedCategory.Q.map f)) :=
    (NatIso.isIso_map_iff (derivedComplexCompletionComparison R a) f).mpr
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr hq)
  exact (F.map_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))).of_iso
    (asIso (F.map (DerivedCategory.Q.map f)))



open Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (J : Ideal R)

private theorem completedKernelTensorRight_isZero_of_almostZero
    (X : Complex R)
    (hX : ∀ i : ℤ, SerrePositivity.Almost.IsAlmostZero
      (perfectoidKernel p R hR J) (X.homology i)) :
    IsZero (completedTensorRight (p : R)
      ((moduleFreeCochainResolution R).obj (ModuleCat.of R (perfectoidKernel p R hR J))) X) := by
  let K := perfectoidKernel p R hR J
  let P := (moduleFreeCochainResolution R).obj (ModuleCat.of R K)
  let F := derivedComplexCompletionFunctor R (p : R)
  have hP : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff _ _).mpr
    (moduleFreeCochainResolution_isZero R (ModuleCat.of R K))
  have hk : complexKFlat R P := complexKFlat_of_flat_boundedAbove R P 0
    (moduleFreeCochainResolution_isZero R (ModuleCat.of R K)) (fun n ↦ by
      let := moduleFreeCochainResolution_free R (ModuleCat.of R K) n
      infer_instance)
  apply completedTensorRight_isZero_of_homology (p : R) P X hk hP
  intro i
  let N := X.homology i
  have h := perfectoidKernel_completedTensor_isZero_of_isAlmostZero p R hR J N (hX i)
  have h' : IsZero (F.obj (DerivedCategory.Q.obj
      (cochainTensor P ((moduleFreeCochainResolution R).obj N)))) :=
    h.of_iso (completedTensorResolutionIso R (p : R) (ModuleCat.of R K) N).symm
  have := moduleFreeCochainAugmentation_quasiIso R N
  have := complexKFlat_quasiIso_right R hk (moduleFreeCochainAugmentation R N)
  exact h'.of_iso (F.mapIso (DerivedCategory.Q.mapIso (β_ (cochainSingleZero N) P) ≪≫
    (asIso (DerivedCategory.Q.map
      (cochainTensorMap (𝟙 P) (moduleFreeCochainAugmentation R N)))).symm))

set_option linter.unusedVariables false in
/-- BS 著者版 Proposition 10.4 の完備複体の almost 零性を、核とのテンソルで判定する。 -/
theorem isAlmostZero_iff_completedTensor_isZero
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsJAlmostZero p R hR J M ↔ IsZero ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨kernelTensor p R hR J M⟩) := by
  refine ⟨fun h ↦ ?_, fun h ↦ isAlmostZero_of_completedTensor_isZero p hR J M hM h⟩
  let X := (M.obj 0).val
  let P := (moduleFreeCochainResolution R).obj (ModuleCat.of R (perfectoidKernel p R hR J))
  let F := derivedComplexCompletionFunctor R (p : R)
  have hX (i : ℤ) : SerrePositivity.Almost.IsAlmostZero
      (perfectoidKernel p R hR J) (X.homology i) :=
    SerrePositivity.Almost.IsAlmostZero.of_equiv
      (derivedInfinityHomologyIso R i M).toLinearEquiv (h i)
  have hz := completedKernelTensorRight_isZero_of_almostZero p hR J X hX
  exact hz.of_iso ((derivedInfinityHomotopyEquivalence R).counitIso.app _ ≪≫
    F.mapIso (DerivedCategory.Q.mapIso (β_ P X)))



/-- almost 連結性から、核との完備テンソルの連結性を得る。 -/
theorem kernelTensor_isLE_of_almostConnective (M : DVertex R)
    (hM : IsAlmostConnective p R hR J M) :
    ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨kernelTensor p R hR J M⟩).IsLE 0 := by
  let X := (M.obj 0).val
  let P := (moduleFreeCochainResolution R).obj (ModuleCat.of R (perfectoidKernel p R hR J))
  let F := derivedComplexCompletionFunctor R (p : R)
  let C := X.truncGE 1
  have hC (i : ℤ) : SerrePositivity.Almost.IsAlmostZero
      (perfectoidKernel p R hR J) (C.homology i) := by
    by_cases hi : 0 < i
    · have he : IsIso ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) i).map
          (X.πTruncGE 1)) := (quasiIsoAt_iff_isIso_homologyMap _ _).mp
        (X.quasiIsoAt_πTruncGE 1 i (by omega))
      let iso := derivedInfinityHomologyIso R i M ≪≫
        asIso ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) i).map
          (X.πTruncGE 1))
      exact SerrePositivity.Almost.IsAlmostZero.of_equiv iso.toLinearEquiv (hM i hi)
    · have hge : C.IsGE 1 := inferInstance
      have hz := ((CochainComplex.isGE_iff C 1).mp hge i (by omega)).isZero_homology
      exact SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
        (fun _ _ _ ↦ (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _)
  have hz := completedKernelTensorRight_isZero_of_almostZero p hR J C hC
  have hp0 : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff _ _).mpr
    (moduleFreeCochainResolution_isZero R _)
  have hp : complexKFlat R P := complexKFlat_of_flat_boundedAbove R P 0
    (moduleFreeCochainResolution_isZero R _) (fun n ↦ by
      let := moduleFreeCochainResolution_free R (ModuleCat.of R (perfectoidKernel p R hR J)) n
      infer_instance)
  let S := X.shortComplexTruncLE 0
  let f := X.ιTruncLE 0
  have hs := X.shortComplexTruncLE_shortExact 0
  let g : mappingCone f ⟶ S.X₃ := mappingCone.descShortComplex S
  have hg : QuasiIso g := mappingCone.quasiIso_descShortComplex hs
  let t := X.shortComplexTruncLEX₃ToTruncGE 0 1
  have ht : QuasiIso t := inferInstance
  have hgt := complexKFlat_quasiIso_left R hp (g ≫ t)
  let T := F.mapTriangle.obj
    ((DerivedCategory.Q : Complex R ⥤ _).mapTriangle.obj
      (mappingCone.triangle (cochainTensorMap f (𝟙 P))))
  have hT : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished (cochainTensorMap f (𝟙 P)))
  have h₃ : IsZero T.obj₃ := hz.of_iso (F.mapIso (DerivedCategory.Q.mapIso
    (cochainTensorConeLeft f P).symm ≪≫ asIso (DerivedCategory.Q.map
      (cochainTensorMap (g ≫ t) (𝟙 P)))))
  have hiso := (T.isZero₃_iff_isIso₁ hT).mp h₃
  have := cochainTensor_isStrictlyLE (X.truncLE 0) P 0 0
  have hc : (DerivedCategory.Q.obj (cochainTensor (X.truncLE 0) P)).IsLE 0 := by
    have h : (DerivedCategory.Q.obj (cochainTensor (X.truncLE 0) P)).IsLE (0 + 0) :=
      inferInstance
    simpa using h
  have : T.obj₁.IsLE 0 := derivedComplexCompletionFunctor_isLE R (p : R) _ _ hc
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso T.mor₁ ≪≫ F.mapIso (DerivedCategory.Q.mapIso (β_ X P)) ≪≫
      ((derivedInfinityHomotopyEquivalence R).counitIso.app _).symm) 0

set_option linter.unusedVariables false in
/-- BS 著者版 Lemma 10.5 の比較に使う almost 連結性の判定。 -/
theorem isAlmostConnective_iff_completedTensor_connective
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsAlmostConnective p R hR J M ↔ Derived.IsConnectiveAt R 0 (kernelTensor p R hR J M) :=
  ⟨fun h ↦ (isConnectiveAt_iff_isLE 0 _).mpr
    (kernelTensor_isLE_of_almostConnective p hR J M h),
    almostConnective_of_kernelTensor_connective p hR J M hM⟩

/-- BS 著者版 Lemma 10.5。連結性を商との完備テンソルと almost 連結性で判定する。 -/
theorem connective_iff_almost
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    Derived.IsConnectiveAt R 0 M ↔ Derived.IsConnectiveAt R 0 (quotientTensor p hR J M) ∧
      IsAlmostConnective p R hR J M := by
  constructor
  · intro h
    refine ⟨(isConnectiveAt_iff_isLE 0 _).mpr ?_, ?_⟩
    · have hB := isLE_moduleHeartVertex (ModuleCat.of R (QuotientPerfectoidization R J p hR))
      have hM' := (isConnectiveAt_iff_isLE 0 M).mp h
      simpa only [add_zero] using completedModuleTensor_isLE p _ M 0 0 hB hM'
    · intro i hi
      exact SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
        (fun _ _ _ ↦ (h i hi).elim _ _)
  · rintro ⟨hB, hK⟩
    exact connective_of_kernelTensor_and_quotientTensor p hR J M hM
      ((isAlmostConnective_iff_completedTensor_connective p hR J hJ M hM).mp hK) hB

end SerrePositivity.BhattScholze.Almost
