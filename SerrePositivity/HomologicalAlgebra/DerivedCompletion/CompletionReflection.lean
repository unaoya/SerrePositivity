module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.CoaugmentedReflection
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 導来完備化の普遍性と完全三角形

## 概要

完備化が標準の単位に沿って全ての冪 Koszul 商を保つこと（`complexCompletionReductionIso`）、実際の主元導来完備化の Hom の普遍性（`derivedComplexCompletionHomEquiv`）を示し、完備対象の充満部分圏への反映として完全三角形を保つこと（`completeReflector`）と、導来圏の上の Koszul の簡約を与える。

## 方針

スカラーの錐の関手が標準の再構成の短完全列を保ち、その第三項が冪 Koszul の商で消えることを使う。正則性は仮定しない。

## 規約

旧 `CompletionReduction`・`ComplexCompletionReflection`・`CompletionTriangulated`・`DerivedKoszulReduction`。

## 使われ方

`BoundedAboveCompletion`・`CompletionMonoidal`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section CompletionReductionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- The inclusion from the constant holim into completion becomes an isomorphism modulo Koszul. -/
lemma complexCompletionTowerInclusion_koszul_isIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    IsIso (DerivedCategory.Q.map
      ((scalarConeFunctor (a ^ n)).map (complexCompletionTowerInclusion R a K))) := by
  let hS := scalarConeFunctor_shortExact (a ^ n)
    (complexCompletionReconstructionSequence R a K)
    (complexCompletionReconstructionSequence_shortExact R a K)
  apply (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)).mp
  exact scalarComplexTowerHomotopyLimit_koszul_isZero R a (K⟦(1 : ℤ)⟧) n

/-- The standard completion unit preserves every power-Koszul quotient, for arbitrary complexes. -/
lemma complexCompletionUnit_koszul_quasiIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    QuasiIso ((scalarConeFunctor (a ^ n)).map (complexCompletionUnit R a K)) := by
  have := constantComplexTowerUnit_quasiIso R K
  have := scalarConeFunctor_map_quasiIso R (a ^ n) (constantComplexTowerUnit R K)
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    (complexCompletionTowerInclusion_koszul_isIso R a K n)
  rw [← constantComplexTowerUnit_comp_completionInclusion, CategoryTheory.Functor.map_comp]
  infer_instance

/-- The reduction isomorphism is the actual image of the standard completion unit. -/
def complexCompletionReductionIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (complexPowerKoszulStage R a K n) ≅
      DerivedCategory.Q.obj
        (complexPowerKoszulStage R a ((complexCompletionFunctor R a).obj K) n) := by
  have := complexCompletionUnit_koszul_quasiIso R a K n
  exact asIso (DerivedCategory.Q.map
    ((scalarConeFunctor (a ^ n)).map (complexCompletionUnit R a K)))

end SerrePositivity.DerivedCompletion

end CompletionReductionPart

section ComplexCompletionReflectionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Completion inverts a map whenever all its power-Koszul reductions are quasi-isomorphisms. -/
theorem complexCompletionFunctor_map_quasiIso_of_koszul
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : ∀ n : ℕ, QuasiIso ((scalarConeFunctor (a ^ n)).map f)) :
    QuasiIso ((complexCompletionFunctor R a).map f) := by
  change QuasiIso
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (CochainComplex.quasiIso_shift_iff _ _).mpr
  have h : QuasiIso ((complexPowerKoszulProductFunctor R a).map f) :=
    complexTowerProductMap_quasiIso R _ hf
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).left) := h
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).right) := h
  exact cochainMappingConeFunctor_map_quasiIso R
    ((complexPowerKoszulDifferenceFunctor R a).map f)

/-- Applying completion to its own standard unit is a quasi-isomorphism on complexes. -/
theorem complexCompletionFunctor_map_unit_quasiIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso ((complexCompletionFunctor R a).map (complexCompletionUnit R a K)) :=
  complexCompletionFunctor_map_quasiIso_of_koszul R a _
    (complexCompletionUnit_koszul_quasiIso R a K)

/-- The actual derived completion functor inverts its standard unit. -/
theorem derivedComplexCompletionFunctor_map_unit_isIso
    (X : ConcreteDerivedCategory R) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((derivedComplexCompletionUnit R a).app X)) := by
  let F := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  have hQ (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      IsIso (F.map (η.app (DerivedCategory.Q.obj K))) := by
    have := complexCompletionFunctor_map_unit_quasiIso R a K
    have hn := (derivedComplexCompletionComparison R a).hom.naturality
      (complexCompletionUnit R a K)
    change F.map (DerivedCategory.Q.map (complexCompletionUnit R a K)) ≫
      (derivedComplexCompletionComparison R a).hom.app
        ((complexCompletionFunctor R a).obj K) =
      (derivedComplexCompletionComparison R a).hom.app K ≫
        DerivedCategory.Q.map ((complexCompletionFunctor R a).map
          (complexCompletionUnit R a K)) at hn
    have hunit : IsIso (F.map (DerivedCategory.Q.map (complexCompletionUnit R a K))) := by
      have : IsIso (F.map (DerivedCategory.Q.map (complexCompletionUnit R a K)) ≫
          (derivedComplexCompletionComparison R a).hom.app
            ((complexCompletionFunctor R a).obj K)) := by
        rw [hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((derivedComplexCompletionComparison R a).hom.app
          ((complexCompletionFunctor R a).obj K))
    have he := congrArg F.map (derivedComplexCompletionUnit_comparison R a K)
    rw [F.map_comp] at he
    have : IsIso (F.map (η.app (DerivedCategory.Q.obj K)) ≫
        F.map ((derivedComplexCompletionComparison R a).hom.app K)) := by
      rw [he]
      exact hunit
    exact IsIso.of_isIso_comp_right _
      (F.map ((derivedComplexCompletionComparison R a).hom.app K))
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := hQ K
  have hn := congrArg F.map (η.naturality e.hom)
  simp only [Functor.id_map, F.map_comp] at hn
  have : IsIso (F.map e.hom ≫ F.map (η.app X)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) (F.map (η.app X))

/-- The two iterated standard units agree on the actual derived category. -/
theorem derivedComplexCompletionUnit_comm (X : ConcreteDerivedCategory R) :
    (derivedComplexCompletionFunctor R a).map ((derivedComplexCompletionUnit R a).app X) =
      (derivedComplexCompletionUnit R a).app ((derivedComplexCompletionFunctor R a).obj X) := by
  apply coaugmentedUnit_comm_of_isIso
  · intro Y
    exact derivedComplexCompletionUnit_isIso_of_isComplete R a _
      (derivedComplexCompletionFunctor_isComplete R a Y)
  · exact derivedComplexCompletionFunctor_map_unit_isIso R a

/-- Precomposition with the actual standard unit is a bijection into every complete target. -/
def derivedComplexCompletionHomEquiv (X Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) :
    ((derivedComplexCompletionFunctor R a).obj X ⟶ Y) ≃ (X ⟶ Y) := by
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Y hY
  exact coaugmentedHomEquiv _ _ (derivedComplexCompletionUnit_comm R a) X Y

@[simp] theorem derivedComplexCompletionHomEquiv_apply (X Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) (f : (derivedComplexCompletionFunctor R a).obj X ⟶ Y) :
    derivedComplexCompletionHomEquiv R a X Y hY f =
      (derivedComplexCompletionUnit R a).app X ≫ f := rfl

/-- The extension is computed using the original completion functor and standard unit. -/
@[simp] theorem derivedComplexCompletionHomEquiv_symm_apply
    (X Y : ConcreteDerivedCategory R) (hY : IsComplete R a Y) (f : X ⟶ Y) :
    (derivedComplexCompletionHomEquiv R a X Y hY).symm f =
      (derivedComplexCompletionFunctor R a).map f ≫
        (derivedComplexCompletionUnitIso R a Y hY).inv := rfl

/-- Maps to a complete target are equal if they agree along the standard completion unit. -/
theorem derivedComplexCompletionHom_ext {X Y : ConcreteDerivedCategory R}
    (hY : IsComplete R a Y)
    {f g : (derivedComplexCompletionFunctor R a).obj X ⟶ Y}
    (h : (derivedComplexCompletionUnit R a).app X ≫ f =
      (derivedComplexCompletionUnit R a).app X ≫ g) : f = g :=
  (derivedComplexCompletionHomEquiv R a X Y hY).injective h

/-- Every map to a complete target has a unique extension along the actual standard unit. -/
theorem derivedComplexCompletion_existsUnique_extension
    {X Y : ConcreteDerivedCategory R} (hY : IsComplete R a Y) (f : X ⟶ Y) :
    ∃! g : (derivedComplexCompletionFunctor R a).obj X ⟶ Y,
      (derivedComplexCompletionUnit R a).app X ≫ g = f := by
  let e := derivedComplexCompletionHomEquiv R a X Y hY
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro g hg
  exact e.injective (hg.trans (e.apply_symm_apply f).symm)

end SerrePositivity.DerivedCompletion

end ComplexCompletionReflectionPart

section CompletionTriangulatedPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- 実導来圏で導来 a 完備である対象の性質。 -/
def completeProperty : ObjectProperty (ConcreteDerivedCategory R) := IsComplete R a

instance completeProperty_isClosedUnderIsomorphisms :
    (completeProperty R a).IsClosedUnderIsomorphisms where
  of_iso e hX := isComplete_of_iso R a e hX

instance completeProperty_isTriangulated : (completeProperty R a).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, by
    apply isComplete_of_scalar_pow_zero R a _ 0
    exact (isZero_zero _).eq_of_src _ _⟩
  isStableUnderShiftBy n := ⟨fun X hX => isComplete_shift R a hX n⟩
  ext₂' T hT h₁ h₃ :=
    (completeProperty R a).le_isoClosure _ (isComplete_triangle_middle R a T hT h₁ h₃)

/-- 既存の実完備化を導来完備対象の充満部分圏へ持ち上げる。 -/
def completeReflector : ConcreteDerivedCategory R ⥤ (completeProperty R a).FullSubcategory :=
  (completeProperty R a).lift (derivedComplexCompletionFunctor R a)
    (derivedComplexCompletionFunctor_isComplete R a)

/-- 元の完備化単位による Hom の普遍性から得る反映の随伴。 -/
def completeReflectorAdjunction : completeReflector R a ⊣ (completeProperty R a).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ((completeProperty R a).fullyFaithfulι.homEquiv.trans
          (derivedComplexCompletionHomEquiv R a X Y.obj Y.property))
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply InducedCategory.hom_ext
        apply (derivedComplexCompletionHomEquiv R a X' Y.obj Y.property).injective
        change (derivedComplexCompletionHomEquiv R a X' Y.obj Y.property)
            ((derivedComplexCompletionHomEquiv R a X' Y.obj Y.property).symm (f ≫ g)) =
          (derivedComplexCompletionUnit R a).app X' ≫
            ((derivedComplexCompletionFunctor R a).map f ≫
              (derivedComplexCompletionHomEquiv R a X Y.obj Y.property).symm g)
        rw [Equiv.apply_symm_apply]
        rw [← Category.assoc, ← (derivedComplexCompletionUnit R a).naturality f]
        simp only [Functor.id_map, Category.assoc]
        exact congrArg (fun k => f ≫ k)
          ((derivedComplexCompletionHomEquiv R a X Y.obj Y.property).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change (derivedComplexCompletionUnit R a).app X ≫ (f.hom ≫ g.hom) =
          ((derivedComplexCompletionUnit R a).app X ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

instance completeReflector_commShift : (completeReflector R a).CommShift ℤ :=
  (completeReflectorAdjunction R a).leftAdjointCommShift ℤ

instance completeReflectorAdjunction_commShift : (completeReflectorAdjunction R a).CommShift ℤ :=
  (completeReflectorAdjunction R a).commShift_of_rightAdjoint ℤ

instance completeReflector_isTriangulated : (completeReflector R a).IsTriangulated :=
  (completeReflectorAdjunction R a).isTriangulated_leftAdjoint

instance derivedComplexCompletionFunctor_commShift :
    (derivedComplexCompletionFunctor R a).CommShift ℤ :=
  inferInstanceAs ((completeReflector R a ⋙ (completeProperty R a).ι).CommShift ℤ)

instance derivedComplexCompletionFunctor_isTriangulated :
    (derivedComplexCompletionFunctor R a).IsTriangulated :=
  inferInstanceAs ((completeReflector R a ⋙ (completeProperty R a).ι).IsTriangulated)

end SerrePositivity.DerivedCompletion

end CompletionTriangulatedPart

section DerivedKoszulReductionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The scalar cone followed by actual localization inverts all quasi-isomorphisms. -/
lemma scalarConeFunctor_inverts_quasiIso (a : R) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy
      (scalarConeFunctor a ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (scalarConeFunctor_map_quasiIso R a f)

/-- Two-term Koszul reduction as a functor on arbitrary actual derived objects. -/
def derivedScalarConeFunctor (a : R) : ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R :=
  Localization.lift (scalarConeFunctor a ⋙ DerivedCategory.Q)
    (scalarConeFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- The derived Koszul functor agrees naturally with the concrete cone of any representative. -/
def derivedScalarConeComparison (a : R) :
    DerivedCategory.Q ⋙ derivedScalarConeFunctor R a ≅ scalarConeFunctor a ⋙ DerivedCategory.Q :=
  Localization.fac (scalarConeFunctor a ⋙ DerivedCategory.Q)
    (scalarConeFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- Power-Koszul reduction of the standard completion unit, on all actual derived objects. -/
def derivedComplexCompletionReduction (a : R) (n : ℕ) :
    derivedScalarConeFunctor R (a ^ n) ⟶
      derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R (a ^ n) where
  app X := (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app X)
  naturality {X Y} f := by
    change (derivedScalarConeFunctor R (a ^ n)).map f ≫
        (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app Y) =
      (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app X) ≫
        (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionFunctor R a).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (derivedScalarConeFunctor R (a ^ n)).map
      ((derivedComplexCompletionUnit R a).naturality f)

/-- The two representative comparisons identify the derived reduction with the concrete unit. -/
lemma derivedComplexCompletionReduction_comparison (a : R) (n : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K) ≫
        (derivedScalarConeFunctor R (a ^ n)).map
          ((derivedComplexCompletionComparison R a).hom.app K) ≫
        (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K) =
      (derivedScalarConeComparison R (a ^ n)).hom.app K ≫
        (complexCompletionReductionIso R a K n).hom := by
  change (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app _) ≫
      (derivedScalarConeFunctor R (a ^ n)).map _ ≫ _ = _
  rw [← CategoryTheory.Functor.map_comp_assoc, derivedComplexCompletionUnit_comparison]
  exact (derivedScalarConeComparison R (a ^ n)).hom.naturality (complexCompletionUnit R a K)

/-- The reduction of the standard completion unit is an isomorphism for every representative. -/
lemma derivedComplexCompletionReduction_isIso_Q (a : R) (n : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K)) := by
  have hc := derivedComplexCompletionReduction_comparison R a n K
  have : IsIso ((derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K) ≫
      ((derivedScalarConeFunctor R (a ^ n)).map
        ((derivedComplexCompletionComparison R a).hom.app K) ≫
      (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K))) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedScalarConeFunctor R (a ^ n)).map
      ((derivedComplexCompletionComparison R a).hom.app K) ≫
      (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K))

/-- Every actual derived object has the same power-Koszul quotients as its completion. -/
lemma derivedComplexCompletionReduction_isIso (a : R) (n : ℕ) (X : ConcreteDerivedCategory R) :
    IsIso ((derivedComplexCompletionReduction R a n).app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := derivedComplexCompletionReduction_isIso_Q R a n K
  have hn := (derivedComplexCompletionReduction R a n).naturality e.hom
  have : IsIso ((derivedScalarConeFunctor R (a ^ n)).map e.hom ≫
      (derivedComplexCompletionReduction R a n).app X) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedScalarConeFunctor R (a ^ n)).map e.hom) _

/-- The canonical power-Koszul comparison as an isomorphism of actual derived objects. -/
def derivedComplexCompletionReductionIso (a : R) (n : ℕ) (X : ConcreteDerivedCategory R) :
    (derivedScalarConeFunctor R (a ^ n)).obj X ≅
      (derivedScalarConeFunctor R (a ^ n)).obj ((derivedComplexCompletionFunctor R a).obj X) := by
  have := derivedComplexCompletionReduction_isIso R a n X
  exact asIso ((derivedComplexCompletionReduction R a n).app X)

/-- The canonical comparison is natural in all actual derived morphisms. -/
def derivedComplexCompletionReductionNatIso (a : R) (n : ℕ) :
    derivedScalarConeFunctor R (a ^ n) ≅
      derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R (a ^ n) :=
  NatIso.ofComponents (derivedComplexCompletionReductionIso R a n)
    (fun f => (derivedComplexCompletionReduction R a n).naturality f)

end SerrePositivity.DerivedCompletion

end DerivedKoszulReductionPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.3.23" (partial := component) "仮定：通常可換環 R と一元 a の全通常導来圏（Lean が強い：主元完備化の通常の導来模型）。結論：完備対象の充満部分圏への反映を左随伴として構成し、その完全三角形の保存を示す（反映の存在と完全性の部分に一致）。任意斉次 Ore 集合の ∞ t 構造、torsion との同値、指定ファイバー列全体は含まれない。"] _root_.SerrePositivity.DerivedCompletion.completeReflectorAdjunction
attribute [cite HA "7.2.3.23" (partial := component) "仮定：通常可換環 R と一元 a の全通常導来圏（Lean が強い：主元完備化の通常の導来模型）。結論：完備対象の充満部分圏への反映を左随伴として構成し、その完全三角形の保存を示す（反映の存在と完全性の部分に一致）。任意斉次 Ore 集合の ∞ t 構造、torsion との同値、指定ファイバー列全体は含まれない。"] _root_.SerrePositivity.DerivedCompletion.completeReflector_isTriangulated
