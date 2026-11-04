module

public import SerrePositivity.HomologicalAlgebra.LinearYoneda
public import Mathlib.Algebra.Homology.SingleHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import Mathlib.Algebra.Homology.LocalCohomology
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.CommutativeAlgebra.Koszul.Powers
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.RingTheory.Filtration
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.ComplexColimits
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsion
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Koszul 複体の双対による局所コホモロジーの計算

## 概要

Mathlib の Ext の零次を商からの Hom として計算し、標準的に augment した Koszul 分解による Ext の自然な比較を作る。座標の冪のイデアルは局所コホモロジーの共終な系をなし、双対 Koszul 複体の冪の有向系の余極限が局所コホモロジーと比較される。零次では余極限がイデアルの冪ねじれと一致し、双対 Koszul の余極限は係数について完全で入射的な係数で非輪状である。Artin–Rees により深い像はホモロジーの写像を零にし、Koszul の冪の遷移写像のイデアル進の深さを評価する。

## 方針

零次の比較を、完全で入射的に非輪状な係数モデルの次元シフトで全次数へ延ばす（HomologicalAlgebra/Ext/LocalCohomology と同じ枠組み）。

## 規約

局所コホモロジーは Mathlib の `localCohomology` を使う。ExtZeroComparison は `Ext.homEquiv₀`・`Ext.linearEquiv₀` で置き換える候補（refactor-plan §3.4.2）。

## 使われ方

`LocalCohomology/Actions`・`LocalCohomology/BaseChange`、CLMST の局所コホモロジーの消滅。
-/

@[expose] public noncomputable section

universe u v

section ExtZeroComparisonPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A specified projective resolution identifies H0 with its augmentation target. -/
def projectiveResolutionCanonicalH0Iso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) :
    P.complex.homology 0 ≅ X :=
  isoOfQuasiIsoAt P.π 0 ≪≫ singleObjHomologySelfIso (.down ℕ) 0 X

/-- The actual Mathlib Ext0 functor is the represented Hom functor, naturally in coefficients. -/
def projectiveResolutionExtZeroNatIso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) :
    (Ext R (ModuleCat.{u} R) 0).obj (op X) ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj (op X) :=
  projectiveResolutionExtNatIso P 0 ≪≫ chainLinearYonedaZeroHomologyNatIso P.complex ≪≫
    ((linearCoyoneda R (ModuleCat.{u} R)).mapIso (projectiveResolutionCanonicalH0Iso P).op).symm

/-- The canonical H0 normalization respects the standard lift between resolutions. -/
lemma projectiveResolutionCanonicalH0Iso_lift_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    homologyMap (ProjectiveResolution.lift f P Q) 0 ≫ (projectiveResolutionCanonicalH0Iso Q).hom =
      (projectiveResolutionCanonicalH0Iso P).hom ≫ f := by
  change homologyMap (ProjectiveResolution.lift f P Q) 0 ≫
      (homologyMap Q.π 0 ≫ (singleObjHomologySelfIso (.down ℕ) 0 Y).hom) =
    (homologyMap P.π 0 ≫ (singleObjHomologySelfIso (.down ℕ) 0 X).hom) ≫ f
  rw [← Category.assoc, ← homologyMap_comp, ProjectiveResolution.lift_commutes,
    homologyMap_comp, Category.assoc, singleObjHomologySelfIso_hom_naturality,
    ← Category.assoc]

/-- The Ext0 comparison respects the actual first-variable maps as natural coefficient maps. -/
lemma projectiveResolutionExtZeroNatIso_first_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (Ext R (ModuleCat.{u} R) 0).map f.op ≫ (projectiveResolutionExtZeroNatIso P).hom =
      (projectiveResolutionExtZeroNatIso Q).hom ≫
        (linearCoyoneda R (ModuleCat.{u} R)).map f.op := by
  apply NatTrans.ext
  funext J
  let φ := ProjectiveResolution.lift f P Q
  let EP := projectiveResolutionCanonicalH0Iso P
  let EQ := projectiveResolutionCanonicalH0Iso Q
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have hcanon : homologyMap φ 0 ≫ EQ.hom = EP.hom ≫ f :=
    projectiveResolutionCanonicalH0Iso_lift_naturality f P Q
  have hinv : EP.inv ≫ homologyMap φ 0 = f ≫ EQ.inv := by
    apply (cancel_mono EQ.hom).mp
    simp only [Category.assoc, hcanon, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hExt := projectiveResolutionIsoExt_first_naturality f P Q φ
    (ProjectiveResolution.lift_commutes_zero f P Q) J 0
  change ((Ext R (ModuleCat.{u} R) 0).map f.op).app J ≫
      ((P.isoExt 0 J).hom ≫ (chainLinearYonedaZeroHomologyIso P.complex J).hom ≫ F.map EP.inv.op) =
    ((Q.isoExt 0 J).hom ≫ (chainLinearYonedaZeroHomologyIso Q.complex J).hom ≫ F.map EQ.inv.op) ≫
      F.map f.op
  rw [← Category.assoc, hExt]
  simp only [Category.assoc]
  rw [← Category.assoc (homologyMap ((chainLinearYonedaMap φ).app J) 0),
    chainLinearYonedaZeroHomologyIso_chain_naturality]
  simp only [Category.assoc]
  congr 1
  congr 1
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hinv]

/-- Actual Mathlib Ext0 and linear Hom agree naturally in both variables. -/
def extZeroLinearCoyonedaNatIso : Ext R (ModuleCat.{u} R) 0 ≅ linearCoyoneda R (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun X => projectiveResolutionExtZeroNatIso (projectiveResolution X.unop))
    (fun f => projectiveResolutionExtZeroNatIso_first_naturality f.unop
      (projectiveResolution _) (projectiveResolution _))

end SerrePositivity

end ExtZeroComparisonPart

section LocalCohomologyKoszulPowersPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- Coordinatewise n-th powers generate a subideal of the n-th power of the span. -/
lemma powerKoszulIdeal_le_span_pow (n : ℕ) :
    powerKoszulIdeal R z n ≤ Ideal.span (Set.range z) ^ n := by
  apply Ideal.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) n

/-- All coordinate-power ideals have radical containing the support ideal. -/
lemma span_le_powerKoszulIdeal_radical (n : ℕ) :
    Ideal.span (Set.range z) ≤ (powerKoszulIdeal R z n).radical := by
  apply Ideal.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact Ideal.mem_radical_iff.mpr ⟨n, Ideal.subset_span (Set.mem_range_self j)⟩

/-- Conversely, each coordinate-power ideal contains a power of the support ideal. -/
lemma exists_span_pow_le_powerKoszulIdeal [hR : IsNoetherian R R] (n : ℕ) :
    ∃ m : ℕ, Ideal.span (Set.range z) ^ m ≤ powerKoszulIdeal R z n :=
  Ideal.exists_pow_le_of_le_radical_of_fg (span_le_powerKoszulIdeal_radical z n)
    (isNoetherian_def.mp hR _)

/-- The actual descending coordinate-power ideals, indexed contravariantly by natural numbers. -/
def powerKoszulIdealDiagram : ℕᵒᵖ ⥤ Ideal R where
  obj n := powerKoszulIdeal R z (unop n)
  map f := ⟨⟨powerKoszulIdeal_antitone R z f.unop.down.down⟩⟩

/-- The coordinate-power system in the category of ideals with the same support condition. -/
def powerKoszulToSelfLERadical : ℕᵒᵖ ⥤ localCohomology.SelfLERadical (Ideal.span (Set.range z)) :=
  ObjectProperty.lift _ (powerKoszulIdealDiagram z)
    (fun n => span_le_powerKoszulIdeal_radical z (unop n))

instance powerKoszulToSelfLERadical_initial [hR : IsNoetherian R R] :
    Functor.Initial (powerKoszulToSelfLERadical z) where
  out J' := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.property
        (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨(powerKoszulIdeal_le_span_pow z k).trans hk⟩⟩⟩ :
          (powerKoszulToSelfLERadical z).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/-- The Ext colimit over coordinate powers is naturally Mathlib's actual local cohomology. -/
def localCohomologyPowerKoszulIdealNatIso [IsNoetherian R R] (i : ℕ) :
    localCohomology.ofDiagram (powerKoszulIdealDiagram z) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  localCohomology.isoOfFinal (powerKoszulToSelfLERadical z)
      (localCohomology.selfLERadicalDiagram (Ideal.span (Set.range z))) i ≪≫
    localCohomology.isoSelfLERadical (Ideal.span (Set.range z)) i

end SerrePositivity

end LocalCohomologyKoszulPowersPart

section KoszulExtComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R]

/-- Use the standard quotient normalization on the zero-th Koszul homology. -/
def canonicalIsResolutionOfKoszul {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) :
    IsResolutionOf (koszulComplex z) (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) where
  isZero_X := koszulComplex_isZero_X_of_pos z
  projective := koszulComplex_projective_X z
  isZero_homology := hz.isZero
  homologyZeroIso := (koszulCanonicalH0Equiv R z).toModuleIso

/-- The Koszul projective resolution with the actual standard quotient augmentation. -/
def canonicalKoszulResolution {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  (canonicalIsResolutionOfKoszul z hz).toProjectiveResolution

/-- The dual Koszul cochain complex as a functor of arbitrary coefficient modules. -/
abbrev koszulDualModuleFunctor {e : ℕ} (z : Fin e → R) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  chainLinearYonedaFunctor (toChain (koszulComplex z))

/-- Ext is naturally computed by the standard augmented dual Koszul complex. -/
def koszulExtComparison {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z) (i : ℕ) :
    (Ext R (ModuleCat R) i).obj (op (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))) ≅
      koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat R) (.up ℕ) i :=
  projectiveResolutionExtNatIso (canonicalKoszulResolution z hz) i

/-- A list consisting of units equal to one is weakly regular, including on zero modules. -/
lemma isWeaklyRegular_replicate_one (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular M (List.replicate n (1 : R)) := by
  induction n generalizing M with
  | zero => exact .nil R M
  | succ n ih =>
    rw [List.replicate_succ]
    apply RingTheory.Sequence.IsWeaklyRegular.cons
    · intro x y h
      simpa only [one_smul] using h
    · exact ih _

/-- The power-zero Koszul complex is a resolution as well; no proper-ideal condition is added. -/
lemma isKoszulResolution_power_zero {e : ℕ} (z : Fin e → R) :
    IsKoszulResolution (fun j => z j ^ (0 : ℕ)) := by
  apply isKoszulResolution_of_isWeaklyRegular
  simpa only [pow_zero, List.ofFn_const] using
    isWeaklyRegular_replicate_one (R := R) R e

/-- Supply all power resolutions, including the zero-th stage of the actual ideal diagram. -/
lemma isKoszulResolution_all_powers [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z)) (n : ℕ) :
    IsKoszulResolution (fun j => z j ^ n) := by
  cases n with
  | zero => exact isKoszulResolution_power_zero z
  | succ n => exact isKoszulResolution_powers_of_isWeaklyRegular z hz hreg (n + 1) (by omega)

/-- The real dual Koszul transition has the direction required by the Ext direct system. -/
def koszulDualPowerTransition {e : ℕ} (z : Fin e → R) (n : ℕ) :
    koszulDualModuleFunctor (fun j => z j ^ n) ⟶
      koszulDualModuleFunctor (fun j => z j ^ (n + 1)) :=
  chainLinearYonedaMap (restrictionMap (powerKoszulTransition R z n) embUp)

/-- Standard quotient normalization makes the power transition an augmented resolution map. -/
lemma canonicalKoszulResolution_power_transition {e : ℕ} (z : Fin e → R) (n : ℕ)
    (h₀ : IsKoszulResolution (fun j => z j ^ n))
    (h₁ : IsKoszulResolution (fun j => z j ^ (n + 1))) :
    (restrictionMap (powerKoszulTransition R z n) embUp).f 0 ≫
        (canonicalKoszulResolution _ h₀).π.f 0 =
      (canonicalKoszulResolution _ h₁).π.f 0 ≫
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op := by
  apply (canonicalIsResolutionOfKoszul _ h₁).restrictionMap_π_f_zero
    (canonicalIsResolutionOfKoszul _ h₀) (powerKoszulTransition R z n)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact powerKoszulStageH0Equiv_transition R z n x

/-- Ext's standard quotient arrows agree with the actual dual Koszul transitions. -/
lemma koszulExtComparison_power_transition {e : ℕ} (z : Fin e → R) (n i : ℕ)
    (h₀ : IsKoszulResolution (fun j => z j ^ n))
    (h₁ : IsKoszulResolution (fun j => z j ^ (n + 1))) :
    (Ext R (ModuleCat R) i).map
        ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op).op ≫ (koszulExtComparison _ h₁ i).hom =
      (koszulExtComparison _ h₀ i).hom ≫
        Functor.whiskerRight (koszulDualPowerTransition z n)
          (homologyFunctor (ModuleCat R) (.up ℕ) i) := by
  apply NatTrans.ext
  funext M
  exact projectiveResolutionIsoExt_first_naturality _
    (canonicalKoszulResolution _ h₁) (canonicalKoszulResolution _ h₀)
    (restrictionMap (powerKoszulTransition R z n) embUp)
    (canonicalKoszulResolution_power_transition z n h₀ h₁) M i

end SerrePositivity

end KoszulExtComparisonPart

section LocalCohomologyKoszulComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- A direct system of actual dual Koszul cochain functors with their actual power transitions. -/
def koszulDualPowerDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) :=
  Functor.ofSequence (koszulDualPowerTransition z)

/-- The cohomology diagram induced by the actual direct system of dual complexes. -/
def koszulDualPowerHomologyDiagram (i : ℕ) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  koszulDualPowerDiagram z ⋙
    (Functor.whiskeringRight (ModuleCat R) (CochainComplex (ModuleCat R) ℕ) (ModuleCat R)).obj
      (homologyFunctor (ModuleCat R) (.up ℕ) i)

/-- Convert the double-opposite index of Mathlib's Ext diagram to the usual natural index. -/
def powerKoszulExtDiagram (i : ℕ) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ localCohomology.diagram (powerKoszulIdealDiagram z) i

/-- Compatible augmented comparisons give an isomorphism of entire indexed Ext/Koszul systems. -/
def koszulExtPowerDiagramNatIso (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (i : ℕ) : powerKoszulExtDiagram z i ≅ koszulDualPowerHomologyDiagram z i := by
  let α : powerKoszulExtDiagram z i ⟶ koszulDualPowerHomologyDiagram z i :=
    NatTrans.ofSequence (fun n => (koszulExtComparison _ (hres n) i).hom) (by
      intro n
      simp only [koszulDualPowerHomologyDiagram, koszulDualPowerDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_map]
      change (Ext R (ModuleCat R) i).map
          ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
            (homOfLE (Nat.le_succ n)).op).op ≫ (koszulExtComparison _ (hres (n + 1)) i).hom =
        (koszulExtComparison _ (hres n) i).hom ≫
          Functor.whiskerRight (koszulDualPowerTransition z n)
            (homologyFunctor (ModuleCat R) (.up ℕ) i)
      exact koszulExtComparison_power_transition z n i (hres n) (hres (n + 1)))
  exact NatIso.ofComponents (fun n => koszulExtComparison _ (hres n) i)
    (fun f => α.naturality f)

/-- The colimit of dual Koszul cohomology is naturally Mathlib's local-cohomology functor. -/
def koszulDualPowerHomologyColimitNatIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    colimit (koszulDualPowerHomologyDiagram z i) ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  (HasColimit.isoOfNatIso (koszulExtPowerDiagramNatIso z hres i)).symm ≪≫
    Functor.Final.colimitIso (opOp ℕ) (localCohomology.diagram (powerKoszulIdealDiagram z) i) ≪≫
      localCohomologyPowerKoszulIdealNatIso z i

/-- The actual dual Koszul system as cochain complexes of coefficient functors. -/
def koszulDualFunctorComplexDiagram : ℕ ⥤ CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  koszulDualPowerDiagram z ⋙ functorCochainComplexFunctor (ModuleCat.{u} R) (ModuleCat.{u} R)

/-- The categorical colimit of dual Koszul complexes, with coefficient functoriality. -/
def koszulDualColimitComplex : CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  colimit (koszulDualFunctorComplexDiagram z)

/-- View the dual Koszul colimit as actual cochain complexes depending on the coefficient module. -/
def koszulDualColimitFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (koszulDualColimitComplex z).asFunctor

/-- Exact sequential colimits identify colimit homology with local cohomology. -/
def koszulDualColimitHomologyNatIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    (koszulDualColimitComplex z).homology i ≅ localCohomology (Ideal.span (Set.range z)) i :=
  sequentialCochainHomologyColimitIso (koszulDualFunctorComplexDiagram z) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (koszulDualPowerDiagram z)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i)) ≪≫
    koszulDualPowerHomologyColimitNatIso z hres i

/-- The actual dual Koszul colimit computes local cohomology naturally. -/
def koszulLocalCohomologyComparison [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  asFunctorCochainHomologyIso (koszulDualColimitComplex z) i ≪≫
    koszulDualColimitHomologyNatIso z hres i

end SerrePositivity

end LocalCohomologyKoszulComparisonPart

section KoszulDualZeroPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- The chain zero-homology normalization uses the actual standard Koszul quotient map. -/
def koszulChainCanonicalH0Iso :
    (toChain (koszulComplex z)).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.span (Set.range z)) :=
  toChainHomologyIso (koszulComplex z) (koszulComplex_isZero_X_of_pos z) 0 ≪≫
    (koszulCanonicalH0Equiv R z).toModuleIso

/-- Zero dual Koszul cohomology is the actual quotient-Hom functor, naturally in coefficients.
Neither a regularity hypothesis on z nor an injectivity hypothesis on coefficients is used. -/
def koszulDualZeroHomologyNatIso :
    koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj
        (op (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))) :=
  chainLinearYonedaZeroHomologyNatIso (toChain (koszulComplex z)) ≪≫
    ((linearCoyoneda R (ModuleCat.{u} R)).mapIso (koszulChainCanonicalH0Iso z).op).symm

end SerrePositivity

end KoszulDualZeroPart

section ArtinReesHomologyPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Artin--Rees controls inverse images along any injection into a finite module. -/
lemma exists_comap_pow_smul_top_le_of_injective
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R N] (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ n : ℕ,
      (I ^ (n + c) • ⊤ : Submodule R N).comap f ≤ I ^ n • ⊤ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨c, fun n => ?_⟩
  apply (Submodule.map_le_map_iff_of_injective hf _ _).mp
  rw [Submodule.map_comap_eq, inf_comm, hc (n + c) (by omega),
    Nat.add_sub_cancel, Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_mono le_rfl inf_le_right

/-- A map with ideal-power annihilated target kills cycles lying sufficiently deep in an
ambient finite module. No finiteness condition is imposed on its target. -/
lemma exists_pow_deep_image_killed
    {M N H : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup H]
    [Module R M] [Module R N] [Module R H] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) (q : M →ₗ[R] H)
    (e : ℕ) (he : I ^ e ≤ Module.annihilator R H) :
    ∃ k : ℕ, ∀ x : M, f x ∈ (I ^ k • ⊤ : Submodule R N) → q x = 0 := by
  obtain ⟨c, hc⟩ := exists_comap_pow_smul_top_le_of_injective I f hf
  refine ⟨e + c, fun x hx => ?_⟩
  have hkill : (I ^ e • ⊤ : Submodule R M) ≤ LinearMap.ker q := by
    apply Submodule.smul_le.mpr
    intro a ha y _
    change q (a • y) = 0
    rw [q.map_smul, Module.mem_annihilator.mp (he ha)]
  exact hkill (hc e hx)

/-- For a fixed finite target term whose homology is killed by an ideal power, all complex
maps with sufficiently deep images in that term induce the zero homology map. -/
lemma exists_pow_homologyMap_eq_zero_of_deep_image
    {ι : Type v} {c : ComplexShape ι} (L : HomologicalComplex (ModuleCat.{u} R) c)
    (i : ι) [Module.Finite R (L.X i)] (I : Ideal R) (e : ℕ)
    (he : I ^ e ≤ Module.annihilator R (L.homology i)) :
    ∃ k : ℕ, ∀ (K : HomologicalComplex (ModuleCat.{u} R) c) (f : K ⟶ L),
      LinearMap.range (f.f i).hom ≤ (I ^ k • ⊤ : Submodule R (L.X i)) →
        homologyMap f i = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_deep_image_killed I (L.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) (L.homologyπ i).hom e he
  refine ⟨k, fun K f hf => ?_⟩
  rw [← cancel_epi (K.homologyπ i), comp_zero, homologyπ_naturality]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hk (cyclesMap f i x)
  have h := hf (LinearMap.mem_range_self (f.f i).hom (K.iCycles i x))
  have heq := congrArg (fun g => g x) (cyclesMap_i f i)
  exact heq.symm ▸ h

/-- For each actual power Koszul stage, sufficiently deep images induce zero maps on its
homology, without any regularity assumption on the parameter sequence. -/
lemma powerKoszul_homologyMap_eq_zero_of_deep_image {e : ℕ} (z : Fin e → R)
    (n : ℕ) (q : ℤ) :
    ∃ k : ℕ, ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
      (f : K ⟶ DerivedCompletion.powerKoszulTower R z n),
      LinearMap.range (f.f q).hom ≤
          (Ideal.span (Set.range z) ^ k • ⊤ : Submodule R
            ((DerivedCompletion.powerKoszulTower R z n).X q)) →
        homologyMap f q = 0 := by
  have h := span_le_annihilator_koszulModuleHomology
    (fun j => z j ^ n) (ModuleCat.of R R) q
  change Ideal.span (Set.range (fun j => z j ^ n)) ≤ Module.annihilator R
    ((koszulComplexOn (fun j => z j ^ n)
      ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj
        (ModuleCat.of R R))).homology q) at h
  rw [koszulComplexOn_single] at h
  obtain ⟨m, hm⟩ := exists_span_pow_le_powerKoszulIdeal z n
  let : Module.Finite R ((DerivedCompletion.powerKoszulTower R z n).X q) :=
    (koszulComplex_free_finite_X (fun j => z j ^ n) q).2
  exact exists_pow_homologyMap_eq_zero_of_deep_image
    (DerivedCompletion.powerKoszulTower R z n) q (Ideal.span (Set.range z)) m (hm.trans h)

end SerrePositivity

end ArtinReesHomologyPart

section KoszulTransitionDepthPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber DerivedCompletion
variable {R : Type u} [CommRing R]

/-- If both diagonal entries have image in I, so does the actual cone-map component. -/
lemma moduleConeArrowMap_range_le_ideal_smul
    {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P ⟶ Q) (ψ : P' ⟶ Q') (α : Arrow.mk φ ⟶ Arrow.mk ψ)
    (I : Ideal R) (q : ℤ)
    (hleft : LinearMap.range (α.left.f (q + 1)).hom ≤ I • ⊤)
    (hright : LinearMap.range (α.right.f q).hom ≤ I • ⊤) :
    LinearMap.range
      ((mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q).hom ≤ I • ⊤ := by
  rintro _ ⟨x, rfl⟩
  let f := (mapArrowHom φ ψ (fun k => ⟨k - 1, by simp⟩) α).f q
  have hx : inlX φ (q + 1) q rfl (fstX φ q (q + 1) rfl x) +
      inrX φ q (sndX φ q x) = x :=
    congrArg (fun g => g x) (moduleCone_coordinates_total φ q (q + 1) rfl)
  change f x ∈ I • ⊤
  rw [← hx, map_add]
  have h₁ := congrArg (fun g => g (fstX φ q (q + 1) rfl x))
    (moduleConeArrowMap_inl φ ψ α q (q + 1) rfl)
  have h₂ := congrArg (fun g => g (sndX φ q x))
    (moduleConeArrowMap_inr φ ψ α q)
  apply Submodule.add_mem
  · rw [show f (inlX φ (q + 1) q rfl (fstX φ q (q + 1) rfl x)) =
      inlX ψ (q + 1) q rfl (α.left.f (q + 1) (fstX φ q (q + 1) rfl x)) from h₁]
    exact Submodule.smul_top_le_comap_smul_top I (inlX ψ (q + 1) q rfl).hom
      (hleft (LinearMap.mem_range_self _ _))
  · rw [show f (inrX φ q (sndX φ q x)) =
      inrX ψ q (α.right.f q (sndX φ q x)) from h₂]
    exact Submodule.smul_top_le_comap_smul_top I (inrX ψ q).hom
      (hright (LinearMap.mem_range_self _ _))

/-- When all multipliers lie in I, a Koszul coordinate map has image in I in negative degrees. -/
lemma koszulComplexMapOfMul_negative_range_le_ideal_smul :
    ∀ {e : ℕ} (a b c : Fin e → R) (h : ∀ j, a j = b j * c j)
      (I : Ideal R) (_hc : ∀ j, c j ∈ I) (q : ℤ), q < 0 →
      LinearMap.range ((koszulComplexMapOfMul R a b c h).f q).hom ≤ I • ⊤ := by
  intro e
  induction e with
  | zero =>
    intro a b c h I hc q hq
    have hz := koszulComplex_isZero_X_of_lt b q (by simpa using hq)
    have hzero : (koszulComplexMapOfMul R a b c h).f q = 0 := hz.eq_of_tgt _ _
    simp [hzero]
  | succ e ih =>
    intro a b c h I hc q hq
    apply moduleConeArrowMap_range_le_ideal_smul
    · rintro _ ⟨x, rfl⟩
      change c (Fin.last e) •
        (koszulComplexMapOfMul R (Fin.init a) (Fin.init b) (Fin.init c)
          (fun j => h j.castSucc)).f (q + 1) x ∈ I • ⊤
      exact Submodule.smul_mem_smul (hc (Fin.last e)) Submodule.mem_top
    · exact ih (Fin.init a) (Fin.init b) (Fin.init c) (fun j => h j.castSucc)
        I (fun j => hc j.castSucc) q hq

/-- Every adjacent power transition has image in the parameter ideal in negative degrees. -/
lemma powerKoszulTransition_negative_range_le_span {e : ℕ} (z : Fin e → R)
    (n : ℕ) (q : ℤ) (hq : q < 0) :
    LinearMap.range ((powerKoszulTransition R z n).f q).hom ≤
      Ideal.span (Set.range z) • ⊤ :=
  koszulComplexMapOfMul_negative_range_le_ideal_smul _ _ _ _ _
    (fun j => Ideal.subset_span (Set.mem_range_self j)) q hq

/-- Ideal-adic depths add when linear maps are composed. -/
lemma linearMap_range_comp_le_pow_smul_top
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (a b : ℕ)
    (hf : LinearMap.range f ≤ I ^ a • ⊤) (hg : LinearMap.range g ≤ I ^ b • ⊤) :
    LinearMap.range (g.comp f) ≤ I ^ (a + b) • ⊤ := by
  rw [LinearMap.range_comp]
  calc
    Submodule.map g (LinearMap.range f) ≤ Submodule.map g (I ^ a • ⊤) :=
      Submodule.map_mono hf
    _ = I ^ a • LinearMap.range g := by rw [Submodule.map_smul'', Submodule.map_top]
    _ ≤ I ^ a • (I ^ b • ⊤) := Submodule.smul_mono le_rfl hg
    _ = I ^ (a + b) • ⊤ := by rw [← Submodule.mul_smul, ← pow_add]

/-- The actual inverse sequence obtained by composing the original adjacent power transitions. -/
def powerKoszulInverseDiagram {e : ℕ} (z : Fin e → R) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.ofOpSequence (powerKoszulTransition R z)

/-- A k-step original power transition has image in the k-th parameter-ideal power. -/
lemma powerKoszulInverseDiagram_negative_range_le_span_pow {e : ℕ} (z : Fin e → R)
    (n k : ℕ) (q : ℤ) (hq : q < 0) :
    LinearMap.range (((powerKoszulInverseDiagram z).map
      (homOfLE (show n ≤ n + k by omega)).op).f q).hom ≤
        Ideal.span (Set.range z) ^ k • ⊤ := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have heq : (homOfLE (show n ≤ n + (k + 1) by omega)).op =
        (homOfLE (show n + k ≤ n + k + 1 by omega)).op ≫
          (homOfLE (show n ≤ n + k by omega)).op := Subsingleton.elim _ _
    rw [heq, Functor.map_comp]
    change LinearMap.range
      ((((powerKoszulInverseDiagram z).map (homOfLE (show n ≤ n + k by omega)).op).f q).hom.comp
        (((powerKoszulInverseDiagram z).map
          (homOfLE (show n + k ≤ n + k + 1 by omega)).op).f q).hom) ≤ _
    apply le_trans (linearMap_range_comp_le_pow_smul_top
      (Ideal.span (Set.range z)) _ _ 1 k _ ih)
    · simp [Nat.add_comm]
    · simpa only [powerKoszulInverseDiagram, Functor.ofOpSequence_map_homOfLE_succ, pow_one]
        using powerKoszulTransition_negative_range_le_span z (n + k) q hq

/-- Arbitrary parameter sequences over Noetherian rings have pro-zero positive Koszul homology,
for the actual inverse system of power transitions. -/
lemma powerKoszul_negative_homology_proZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (q : ℤ) (hq : q < 0) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      homologyMap ((powerKoszulInverseDiagram z).map (homOfLE hnm).op) q = 0 := by
  obtain ⟨k, hk⟩ := powerKoszul_homologyMap_eq_zero_of_deep_image z n q
  exact ⟨n + k, by omega, hk _ _
    (powerKoszulInverseDiagram_negative_range_le_span_pow z n k q hq)⟩

end SerrePositivity

end KoszulTransitionDepthPart

section KoszulDualInjectiveAcyclicPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open Opposite DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Read the actual inverse Koszul diagram as a direct diagram of dual coefficient functors. -/
def koszulDualInverseDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) where
  obj n := koszulDualModuleFunctor (fun j => z j ^ n)
  map f := chainLinearYonedaMap
    (restrictionMap ((powerKoszulInverseDiagram z).map f.op) embUp)
  map_id n := by
    change chainLinearYonedaMap
      (restrictionMap ((powerKoszulInverseDiagram z).map (𝟙 (op n))) embUp) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, restrictionMap_id]
    exact chainLinearYonedaMap_id (toChain (powerKoszulTower R z n))
  map_comp f g := by simp [chainLinearYonedaMap_comp]

/-- All maps of the existing direct diagram are duals of the original composed inverse maps. -/
lemma koszulDualPowerDiagram_map_eq_inverse {n m : ℕ} (f : n ⟶ m) :
    (koszulDualPowerDiagram z).map f =
      chainLinearYonedaMap
        (restrictionMap ((powerKoszulInverseDiagram z).map f.op) embUp) := by
  let α : koszulDualPowerDiagram z ⟶ koszulDualInverseDiagram z :=
    NatTrans.ofSequence (fun _ => 𝟙 _) (by
      intro k
      simp [koszulDualPowerDiagram, koszulDualInverseDiagram,
        powerKoszulInverseDiagram, koszulDualPowerTransition])
  simpa [α, koszulDualInverseDiagram] using α.naturality f

/-- With injective coefficients, every positive dual cohomology transition eventually vanishes. -/
lemma koszulDualPowerDiagram_injective_homology_eventually_zero [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      homologyMap (((koszulDualPowerDiagram z).map (homOfLE hnm)).app J) i = 0 := by
  obtain ⟨m, hnm, hm⟩ := powerKoszul_negative_homology_proZero z (-(i : ℤ)) (by omega) n
  let f : powerKoszulTower R z m ⟶ powerKoszulTower R z n :=
    (powerKoszulInverseDiagram z).map (homOfLE hnm).op
  have hchain : homologyMap (restrictionMap f embUp) i = 0 := by
    apply (cancel_mono (toChainHomologyIso (powerKoszulTower R z n)
      (koszulComplex_isZero_X_of_pos _) i).hom).mp
    erw [zero_comp, toChainHomologyIso_hom_naturality f
      (koszulComplex_isZero_X_of_pos _) (koszulComplex_isZero_X_of_pos _), hm, comp_zero]
  refine ⟨m, hnm, ?_⟩
  rw [koszulDualPowerDiagram_map_eq_inverse]
  exact chainLinearYonedaMap_homology_eq_zero_of_injective
    (restrictionMap f embUp) J i hchain

/-- An eventually-zero sequential diagram has zero colimit. -/
lemma sequentialModuleColimit_isZero_of_eventually_zero (F : ℕ ⥤ ModuleCat.{u} R)
    (hF : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, F.map (homOfLE hnm) = 0) :
    IsZero (colimit F) := by
  have hι : ∀ n : ℕ, colimit.ι F n = 0 := by
    intro n
    obtain ⟨m, hnm, hm⟩ := hF n
    rw [← colimit.w F (homOfLE hnm), hm, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro n
  simp [hι n]

/-- The actual colimit homology comparison before any regular-sequence Ext computation. -/
def koszulDualColimitHomologyDiagramIso (i : ℕ) :
    (koszulDualColimitComplex z).homology i ≅ colimit (koszulDualPowerHomologyDiagram z i) :=
  sequentialCochainHomologyColimitIso (koszulDualFunctorComplexDiagram z) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (koszulDualPowerDiagram z)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i))

/-- On injective coefficient modules, the actual dual Koszul colimit has no positive cohomology.
No regularity on the finite parameter sequence is required. -/
lemma koszulDualColimit_injective_positive_homology_isZero [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((koszulDualColimitFunctor z).obj J).homology i) := by
  let E := (asFunctorCochainHomologyIso (koszulDualColimitComplex z) i).app J ≪≫
    (koszulDualColimitHomologyDiagramIso z i).app J ≪≫
    colimitObjIsoColimitCompEvaluation (koszulDualPowerHomologyDiagram z i) J
  apply IsZero.of_iso _ E
  apply sequentialModuleColimit_isZero_of_eventually_zero
  intro n
  obtain ⟨m, hnm, hm⟩ := koszulDualPowerDiagram_injective_homology_eventually_zero z J i hi n
  exact ⟨m, hnm, hm⟩

end SerrePositivity

end KoszulDualInjectiveAcyclicPart

section KoszulDualZeroTransitionsPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite HomologicalComplex
open DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- The actual chain H0 quotient normalization respects the original adjacent power maps. -/
lemma koszulChainCanonicalH0Iso_power_transition (n : ℕ) :
    homologyMap (restrictionMap (powerKoszulTransition R z n) embUp) 0 ≫
        (koszulChainCanonicalH0Iso (fun j => z j ^ n)).hom =
      (koszulChainCanonicalH0Iso (fun j => z j ^ (n + 1))).hom ≫
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op := by
  dsimp only [koszulChainCanonicalH0Iso, Iso.trans_hom]
  erw [← Category.assoc, toChainHomologyIso_hom_naturality (powerKoszulTransition R z n)
    (koszulComplex_isZero_X_of_pos _) (koszulComplex_isZero_X_of_pos _), Category.assoc]
  rw [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact powerKoszulStageH0Equiv_transition R z n x

/-- Zero dual cohomology identifies each actual power transition with precomposition by
its standard quotient transition, naturally in every coefficient module. -/
lemma koszulDualZeroHomologyNatIso_power_transition (n : ℕ) :
    Functor.whiskerRight (koszulDualPowerTransition z n)
        (homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0) ≫
        (koszulDualZeroHomologyNatIso (fun j => z j ^ (n + 1))).hom =
      (koszulDualZeroHomologyNatIso (fun j => z j ^ n)).hom ≫
        (linearCoyoneda R (ModuleCat.{u} R)).map
          ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
            (homOfLE (Nat.le_succ n)).op).op := by
  apply NatTrans.ext
  funext J
  let K := toChain (powerKoszulTower R z (n + 1))
  let L := toChain (powerKoszulTower R z n)
  let f : K ⟶ L := restrictionMap (powerKoszulTransition R z n) embUp
  let EK := koszulChainCanonicalH0Iso (fun j => z j ^ (n + 1))
  let EL := koszulChainCanonicalH0Iso (fun j => z j ^ n)
  let q := (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
    (homOfLE (Nat.le_succ n)).op
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have hnorm : homologyMap f 0 ≫ EL.hom = EK.hom ≫ q :=
    koszulChainCanonicalH0Iso_power_transition z n
  have hinv : EK.inv ≫ homologyMap f 0 = q ≫ EL.inv := by
    apply (cancel_mono EL.hom).mp
    simp only [Category.assoc, hnorm, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
      ((chainLinearYonedaZeroHomologyIso K J).hom ≫ F.map EK.inv.op) =
    ((chainLinearYonedaZeroHomologyIso L J).hom ≫ F.map EL.inv.op) ≫ F.map q.op
  rw [← Category.assoc, chainLinearYonedaZeroHomologyIso_chain_naturality,
    Category.assoc, Category.assoc]
  congr 1
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hinv]

/-- The direct diagram of Hom from the actual coordinate-power quotients. -/
def powerKoszulQuotientHomDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).op ⋙
    linearCoyoneda R (ModuleCat.{u} R)

/-- The entire zero dual cohomology diagram agrees with the quotient-Hom diagram. -/
def koszulDualPowerZeroHomologyDiagramNatIso :
    koszulDualPowerHomologyDiagram z 0 ≅ powerKoszulQuotientHomDiagram z := by
  let α : koszulDualPowerHomologyDiagram z 0 ⟶ powerKoszulQuotientHomDiagram z :=
    NatTrans.ofSequence (fun n => (koszulDualZeroHomologyNatIso (fun j => z j ^ n)).hom) (by
      intro n
      simp only [koszulDualPowerHomologyDiagram, koszulDualPowerDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_map]
      exact koszulDualZeroHomologyNatIso_power_transition z n)
  exact NatIso.ofComponents (fun n => koszulDualZeroHomologyNatIso (fun j => z j ^ n))
    (fun f => α.naturality f)

/-- The zero homology of the actual dual colimit is the actual quotient-Hom colimit,
naturally in coefficients. No Noetherian or regular-sequence assumption is needed. -/
def koszulDualColimitZeroQuotientHomNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      colimit (powerKoszulQuotientHomDiagram z) :=
  asFunctorCochainHomologyIso (koszulDualColimitComplex z) 0 ≪≫
    koszulDualColimitHomologyDiagramIso z 0 ≪≫
    HasColimit.isoOfNatIso (koszulDualPowerZeroHomologyDiagramNatIso z)

end SerrePositivity

end KoszulDualZeroTransitionsPart

section KoszulDualCoefficientExactPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Each actual dual Koszul stage is exact in arbitrary coefficient modules. -/
instance koszulDualModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (koszulDualModuleFunctor z) := by
  have : ∀ i, Projective ((toChain (koszulComplex z)).X i) := fun i =>
    Projective.of_iso ((koszulComplex z).restrictionXIso embUp rfl).symm
      (koszulComplex_projective_X z _)
  exact chainLinearYonedaFunctor_preservesFiniteColimits _

/-- Each actual colimit term preserves finite limits in its coefficients. -/
instance koszulDualColimitTerm_preservesFiniteLimits (i : ℕ) :
    PreservesFiniteLimits ((koszulDualColimitComplex z).X i) := by
  let D := koszulDualFunctorComplexDiagram z ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteLimits (D.obj n) := fun n => by
    change PreservesFiniteLimits (koszulDualModuleFunctor (fun j => z j ^ n) ⋙
      eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteLimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (koszulDualFunctorComplexDiagram z)).symm

/-- Each actual colimit term preserves finite colimits in its coefficients. -/
instance koszulDualColimitTerm_preservesFiniteColimits (i : ℕ) :
    PreservesFiniteColimits ((koszulDualColimitComplex z).X i) := by
  let D := koszulDualFunctorComplexDiagram z ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteColimits (D.obj n) := fun n => by
    change PreservesFiniteColimits (koszulDualModuleFunctor (fun j => z j ^ n) ⋙
      eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteColimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (koszulDualFunctorComplexDiagram z)).symm

/-- The entire actual dual-colimit complex functor preserves finite limits. -/
instance koszulDualColimitFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (koszulDualColimitFunctor z) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((koszulDualColimitComplex z).X i)
      infer_instance)

/-- The entire actual dual-colimit complex functor preserves finite colimits. -/
instance koszulDualColimitFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (koszulDualColimitFunctor z) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((koszulDualColimitComplex z).X i)
      infer_instance)

end SerrePositivity

end KoszulDualCoefficientExactPart

section KoszulDualZeroTorsionPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite HomologicalComplex
open DerivedCompletion
variable {R : Type u} [CommRing R] [IsNoetherian R R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Evaluation at one gives a natural inclusion of each quotient-Hom stage into power torsion. -/
def powerKoszulQuotientHomToTorsion (n : ℕ) :
    (powerKoszulQuotientHomDiagram z).obj n ⟶
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) where
  app M := ModuleCat.ofHom
    { toFun := fun (f : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M) => ⟨f 1, by
        obtain ⟨k, hk⟩ := exists_span_pow_le_powerKoszulIdeal z n
        apply (Ideal.primaryComponent_mem _ _ _).mpr
        refine ⟨k, ?_⟩
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        have hf := (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M f).property
        exact (Submodule.mem_torsionBySet_iff _ _).mp hf ⟨a, hk a.property⟩⟩
      map_add' := by intro f g; apply Subtype.ext; rfl
      map_smul' := by intro r f; apply Subtype.ext; rfl }
  naturality {M N} f := by ext g; rfl

/-- These natural evaluations respect the actual quotient transition maps. -/
def powerKoszulQuotientHomTorsionCocone : Cocone (powerKoszulQuotientHomDiagram z) where
  pt := idealPowerTorsionFunctor (Ideal.span (Set.range z))
  ι := NatTrans.ofSequence (powerKoszulQuotientHomToTorsion z) (by
    intro n
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl)

/-- The natural map from the actual quotient-Hom colimit to the actual power-torsion functor. -/
def quotientHomColimitToPowerTorsion :
    colimit (powerKoszulQuotientHomDiagram z) ⟶
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  colimit.desc _ (powerKoszulQuotientHomTorsionCocone z)

/-- Evaluation is injective at every actual quotient stage. -/
instance powerKoszulQuotientHomToTorsion_mono (n : ℕ) :
    Mono (powerKoszulQuotientHomToTorsion z n) := by
  have : ∀ M : ModuleCat.{u} R, Mono ((powerKoszulQuotientHomToTorsion z n).app M) := by
    intro M
    apply (ModuleCat.mono_iff_injective _).mpr
    intro f g h
    apply (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M).injective
    apply Subtype.ext
    change (f : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M).hom
        (1 : R ⧸ powerKoszulIdeal R z n) =
      (g : ModuleCat.of R (R ⧸ powerKoszulIdeal R z n) ⟶ M).hom
        (1 : R ⧸ powerKoszulIdeal R z n)
    exact congrArg Subtype.val h
  exact NatTrans.mono_of_mono_app _

/-- Exact filtered colimits retain injectivity of the map into the constant torsion functor. -/
instance quotientHomColimitToPowerTorsion_mono : Mono (quotientHomColimitToPowerTorsion z) := by
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : ∀ n, Mono ((powerKoszulQuotientHomTorsionCocone z).ι.app n) := fun n =>
    powerKoszulQuotientHomToTorsion_mono z n
  have := NatTrans.mono_of_mono_app (powerKoszulQuotientHomTorsionCocone z).ι
  exact colim.map_mono' (powerKoszulQuotientHomTorsionCocone z).ι
    (colimit.isColimit _) (isColimitConstCocone ℕ _)
    (quotientHomColimitToPowerTorsion z) (fun n => by simp [quotientHomColimitToPowerTorsion])

/-- Every ideal-power-torsion element is the evaluation of an actual quotient-Hom stage. -/
lemma quotientHomColimitToPowerTorsion_surjective (M : ModuleCat.{u} R) :
    Function.Surjective ((quotientHomColimitToPowerTorsion z).app M) := by
  intro x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ _).mp x.property
  let y : Submodule.torsionBySet R M (powerKoszulIdeal R z n : Set R) := ⟨x.val, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a, powerKoszulIdeal_le_span_pow z n a.property⟩⟩
  let f := (quotientHomEvalOneEquiv (powerKoszulIdeal R z n) M).symm y
  refine ⟨(colimit.ι (powerKoszulQuotientHomDiagram z) n).app M f, ?_⟩
  have h := congrArg (fun α => α.app M)
    (colimit.ι_desc (powerKoszulQuotientHomTorsionCocone z) n)
  have hx := congrArg (fun g => g f) h
  apply Subtype.ext
  rw [show ((quotientHomColimitToPowerTorsion z).app M)
      ((colimit.ι (powerKoszulQuotientHomDiagram z) n).app M f) =
        (powerKoszulQuotientHomToTorsion z n).app M f from hx]
  change f 1 = x.val
  exact quotientHomEvalOneEquiv_symm_apply_one _ _ y

/-- The actual quotient-Hom colimit is precisely the actual ideal-power torsion functor. -/
def quotientHomColimitPowerTorsionNatIso :
    colimit (powerKoszulQuotientHomDiagram z) ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) := by
  have : ∀ M : ModuleCat.{u} R, IsIso ((quotientHomColimitToPowerTorsion z).app M) := by
    intro M
    have : Epi ((quotientHomColimitToPowerTorsion z).app M) :=
      (ModuleCat.epi_iff_surjective _).mpr (quotientHomColimitToPowerTorsion_surjective z M)
    exact isIso_of_mono_of_epi _
  have := NatIso.isIso_of_isIso_app (quotientHomColimitToPowerTorsion z)
  exact asIso (quotientHomColimitToPowerTorsion z)

/-- The actual zero dual-colimit cohomology is actual power torsion, naturally in coefficients. -/
def koszulDualColimitZeroTorsionNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  koszulDualColimitZeroQuotientHomNatIso z ≪≫ quotientHomColimitPowerTorsionNatIso z

end SerrePositivity

end KoszulDualZeroTorsionPart
