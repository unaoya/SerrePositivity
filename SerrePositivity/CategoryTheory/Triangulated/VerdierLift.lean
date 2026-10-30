module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Shift.Linear

/-! # Verdier 商への三角関手の降下

## 概要

対象を零に送る三角関手が Verdier 商を経由すること（シフトとの両立・三角関手であることを含む）、小部分圏を消すホモロジー関手の局所化、シフトで安定な充満部分圏の線形構造、完全忠実な前合成に沿ったシフト両立性の延長を与える。

## 方針

降下は Mathlib の `Localization.lift` と `Functor.commShiftOfLocalization`、三角性は `Functor.IsTriangulated` の補題で作る。前合成に沿ったシフト両立性（`commShiftOfPrecomp`）は Mathlib にない（`Functor.CommShift.ofComp` は後合成の版）。

## 規約

ホモロジー関手の局所化は Mathlib の `Functor.mem_homologicalKernel_trW_iff` を直接使う。

## 使われ方

Verdier 商と完備化の交換、t 構造の局所化、Asymptotic の階数の商、KST・PerfectComplex の商への評価。
-/

@[expose] public noncomputable section

section CommShiftOfPrecompPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor

variable {M : Type*} [AddMonoid M] {B C D : Type*} [Category* B] [Category* C] [Category* D]
  [HasShift B M] [HasShift C M] [HasShift D M]
  (L : B ⥤ C) (F : C ⥤ D) (H : B ⥤ D) (e : L ⋙ F ≅ H)
  [L.CommShift M] [H.CommShift M]
  [((whiskeringLeft B C D).obj L).Full] [((whiskeringLeft B C D).obj L).Faithful]

/-- 前合成後のシフト同型から構成するシフト同型。 -/
noncomputable def precompShiftIso (n : M) : shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n :=
  ((whiskeringLeft B C D).obj L).preimageIso
    (isoWhiskerRight (L.commShiftIso n).symm F ≪≫
      isoWhiskerLeft (shiftFunctor B n) e ≪≫ H.commShiftIso n ≪≫
      isoWhiskerRight e.symm (shiftFunctor D n))

@[simp, reassoc] lemma precompShiftIso_hom_app (n : M) (X : B) :
    (precompShiftIso L F H e n).hom.app (L.obj X) =
      F.map ((L.commShiftIso n).inv.app X) ≫ e.hom.app (X⟦n⟧) ≫
        (H.commShiftIso n).hom.app X ≫ (e.inv.app X)⟦n⟧' := by
  have h : ((whiskeringLeft B C D).obj L).map (precompShiftIso L F H e n).hom =
    (isoWhiskerRight (L.commShiftIso n).symm F ≪≫
      isoWhiskerLeft (shiftFunctor B n) e ≪≫ H.commShiftIso n ≪≫
      isoWhiskerRight e.symm (shiftFunctor D n)).hom := Functor.map_preimage _ _
  exact congr_app h X

attribute [irreducible] precompShiftIso

/-- 関手圏での前合成が完全忠実なら、シフトとの両立を延長できる。 -/
@[instance_reducible] noncomputable def commShiftOfPrecomp : F.CommShift M where
  commShiftIso := precompShiftIso L F H e
  commShiftIso_zero := by
    apply Iso.ext
    apply ((whiskeringLeft B C D).obj L).map_injective
    ext X
    change (precompShiftIso L F H e 0).hom.app (L.obj X) =
      (CommShift.isoZero F M).hom.app (L.obj X)
    simp only [precompShiftIso_hom_app, L.commShiftIso_zero, H.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Functor.map_comp, Category.assoc]
    have hn := e.hom.naturality ((shiftFunctorZero B M).inv.app X)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
    rw [← (shiftFunctorZero D M).inv.naturality]
    simp
  commShiftIso_add a b := by
    apply Iso.ext
    apply ((whiskeringLeft B C D).obj L).map_injective
    ext X
    change (precompShiftIso L F H e (a + b)).hom.app (L.obj X) =
      (CommShift.isoAdd (precompShiftIso L F H e a)
        (precompShiftIso L F H e b)).hom.app (L.obj X)
    simp only [precompShiftIso_hom_app, L.commShiftIso_add, H.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_inv_app,
      Functor.map_comp, Category.assoc]
    have hn := e.hom.naturality ((shiftFunctorAdd B a b).inv.app X)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
    rw [← (shiftFunctorAdd D a b).inv.naturality]
    simp only [Functor.comp_map]
    have hn' := (precompShiftIso L F H e b).hom.naturality
      ((L.commShiftIso a).inv.app X)
    dsimp only [Functor.comp_map] at hn'
    rw [← reassoc_of% hn', precompShiftIso_hom_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp

/-- 構成したシフト両立性では、元の比較同型もシフトと両立する。 -/
lemma commShiftOfPrecomp_compatibility :
    letI := commShiftOfPrecomp (M := M) L F H e
    NatTrans.CommShift e.hom M := by
  let := commShiftOfPrecomp (M := M) L F H e
  refine ⟨fun n ↦ ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app,
    show F.commShiftIso n = precompShiftIso L F H e n from rfl]

end SerrePositivity

end CommShiftOfPrecompPart

section VerdierLiftPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (P : ObjectProperty C) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ X, P X → IsZero (F.obj X))

include hF in
lemma triangulated_inverts_of_kills : P.trW.IsInvertedBy F := by
  intro X Y f hf
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).mp (hF Z hZ)

variable [IsTriangulated C] [P.IsTriangulated]

/-- 部分圏の対象は Verdier 商で零になる。 -/
lemma verdierQuotient_isZero (X : C) (hX : P X) : IsZero (P.trW.Q.obj X) := by
  have hf : P.trW (0 : (0 : C) ⟶ X) :=
    ⟨X, 𝟙 X, 0, contractible_distinguished₁ X, hX⟩
  have := Localization.inverts P.trW.Q P.trW _ hf
  exact IsZero.of_iso (P.trW.Q.map_isZero (isZero_zero C))
    (asIso (P.trW.Q.map (0 : (0 : C) ⟶ X))).symm

@[implicit_reducible]
noncomputable def verdierLift : P.trW.Localization ⥤ D :=
  Localization.lift F (triangulated_inverts_of_kills P F hF) P.trW.Q

noncomputable def verdierLiftFactors : P.trW.Q ⋙ verdierLift P F hF ≅ F :=
  Localization.fac F (triangulated_inverts_of_kills P F hF) P.trW.Q

noncomputable instance verdierLift_lifting :
    Localization.Lifting P.trW.Q P.trW F (verdierLift P F hF) := ⟨verdierLiftFactors P F hF⟩

noncomputable instance verdierLift_commShift : (verdierLift P F hF).CommShift ℤ :=
  Functor.commShiftOfLocalization P.trW.Q P.trW ℤ F (verdierLift P F hF)

instance verdierLiftFactors_commShift : NatTrans.CommShift (verdierLiftFactors P F hF).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization P.trW.Q P.trW ℤ F (verdierLift P F hF)

instance verdierLift_isTriangulated : (verdierLift P F hF).IsTriangulated := by
  let := Localization.essSurj_mapArrow P.trW.Q P.trW
  exact Functor.isTriangulated_of_precomp_iso (verdierLiftFactors P F hF)

end SerrePositivity

end VerdierLiftPart

section HomologicalLocalizationPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]
  (F : C ⥤ A) [F.IsHomological]

/-- シフトで安定な部分圏を消すホモロジー関手は Verdier の分母を反転する。 -/
lemma homological_inverts_of_kills (hF : ∀ X, P X → IsZero (F.obj X)) :
    P.trW.IsInvertedBy F := by
  let := Functor.ShiftSequence.tautological F ℤ
  have hle : P ≤ F.homologicalKernel := by
    intro X hX n
    apply hF
    exact P.le_shift n X hX
  intro X Y f hf
  have h := (F.mem_homologicalKernel_trW_iff f).mp ((P.trW_monotone hle) f hf) 0
  exact (NatIso.isIso_map_iff (F.isoShiftZero ℤ) f).mp h

end SerrePositivity

end HomologicalLocalizationPart

section SubcategoryLinearPart

namespace SerrePositivity

open CategoryTheory

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- 充満部分圏のシフトは、元の圏のシフトの線形性を引き継ぐ。 -/
instance fullSubcategory_shift_linear (n : ℤ) :
    (shiftFunctor P.FullSubcategory n).Linear R := by
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  constructor
  intro X Y f a
  apply P.ι.map_injective
  simpa only [Functor.map_smul, Functor.comp_map] using
    (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul a f

end SerrePositivity

end SubcategoryLinearPart
