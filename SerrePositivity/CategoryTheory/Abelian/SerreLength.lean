module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Basic.Real.Basic

/-! # Serre 部分圏と加法的な長さ

## 概要

Serre 部分圏の閉性とアーベル商、Serre 商への加法的な対象評価の降下、非負で加法的な長さと、長さ 0 の対象のなす Serre 部分圏を与える。

## 方針

Mathlib の `ObjectProperty.IsSerreClass` と SerreClass/Localization に乗せる。商のアーベル性のインスタンス（`P.isoModSerre.Localization`）は Mathlib にない。

## 規約

長さは値を `ℕ∞` などの順序付き加法モノイドにとる。

## 使われ方

LengthAlgebra の Serre 商、Asymptotic の長さの商、CommutativeAlgebra の冪ねじれの圏。
-/

@[expose] public noncomputable section

section SerreSubcategoryPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.IsSerreClass]

/-- Serre 部分圏は二項積で閉じる。直和の分裂短完全列を使う。 -/
instance serre_closedUnderBinaryProducts : P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have h₁ := p.prop_diag_obj (.mk .left)
    have h₂ := p.prop_diag_obj (.mk .right)
    let Y := p.diag.obj (.mk .left)
    let Z := p.diag.obj (.mk .right)
    have hprod : P (Y ⨯ Z) := P.prop_of_iso (biprod.isoProd Y Z) (P.prop_biprod h₁ h₂)
    exact P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (prodIsProd Y Z)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)) hprod

instance serre_closedUnderFiniteProducts : P.IsClosedUnderFiniteProducts := .mk'

/-- Serre 部分圏はアーベル圏である。 -/
noncomputable example : Abelian P.FullSubcategory := inferInstance

/-- Serre 部分圏の包含は有限極限を保つ。 -/
noncomputable instance serreInclusionPreservesFiniteLimits : PreservesFiniteLimits P.ι := by
  have := P.preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- Serre 部分圏の包含は有限余極限を保つ。 -/
noncomputable instance serreInclusionPreservesFiniteColimits : PreservesFiniteColimits P.ι := by
  have := P.preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- 標準的な Serre 商には既存の局所化の構成からアーベル圏構造が入る。 -/
noncomputable instance serreQuotientAbelian : Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P

end SerrePositivity

end SerreSubcategoryPart

section SerreLengthPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {L : Type*} [AddCommMonoid L]
  {C : Type*} [Category* C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass] (l : C → L)
  (hi : ∀ {X Y : C}, (X ≅ Y) → l X = l Y)
  (ha : ∀ {S : ShortComplex C}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
  (hz : ∀ X : C, P X → l X = 0)

include hi ha in
/-- 加法的な評価の核・余核の公式。 -/
lemma additiveLength_kernel_cokernel {X Y : C} (f : X ⟶ Y) :
    l X + l (cokernel f) = l (kernel f) + l Y := by
  have h₁ := ha (show (ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
    (Abelian.comp_coimage_π_eq_zero (kernel.condition f))).ShortExact from
    { exact := (ShortComplex.exact_iff_exact_coimage_π _).mp (ShortComplex.exact_kernel f) })
  have h₂ := ha (show (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (Abelian.image_ι_comp_eq_zero (cokernel.condition f))).ShortExact from
    { exact := (ShortComplex.exact_iff_exact_image_ι _).mp (ShortComplex.exact_cokernel f) })
  have h₃ := hi (Abelian.coimageIsoImage f)
  dsimp only at h₁ h₂
  rw [h₁, h₂, h₃]
  abel

include hi ha hz in
/-- 核と余核が零評価ならば、射の両端は同じ評価をもつ。 -/
lemma additiveLength_eq_of_isoModSerre {X Y : C} (f : X ⟶ Y) (hf : P.isoModSerre f) :
    l X = l Y := by
  have h := additiveLength_kernel_cokernel l hi ha f
  rw [hz _ hf.1, hz _ hf.2, zero_add, add_zero] at h
  exact h

include hi ha hz in
/-- Serre 商の中で同型となる対象の評価は等しい。 -/
lemma additiveLength_eq_of_localization_iso {X Y : C}
    (e : P.isoModSerre.Q.obj X ≅ P.isoModSerre.Q.obj Y) : l X = l Y := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction P.isoModSerre.Q P.isoModSerre e.hom
  have hf : IsIso (P.isoModSerre.Q.map φ.f) := by
    have he : IsIso (φ.map P.isoModSerre.Q (Localization.inverts _ _)) := hφ ▸ inferInstance
    have hcomp : φ.map P.isoModSerre.Q (Localization.inverts _ _) ≫
        P.isoModSerre.Q.map φ.s = P.isoModSerre.Q.map φ.f := by simp
    rw [← hcomp]
    infer_instance
  have hf' := (ObjectProperty.SerreClassLocalization.isIso_map_iff P.isoModSerre.Q P φ.f).mp hf
  exact (additiveLength_eq_of_isoModSerre P l hi ha hz φ.f hf').trans
    (additiveLength_eq_of_isoModSerre P l hi ha hz φ.s φ.hs).symm

/-- 標準局所化の対象の代表元で計算する評価。 -/
noncomputable def serreQuotientLength : P.isoModSerre.Localization → L :=
  fun X ↦ l ((Localization.Construction.objEquiv P.isoModSerre).symm X)

omit [AddCommMonoid L] in
/-- 商関手の像では元の評価と一致する。 -/
@[simp] lemma serreQuotientLength_obj (X : C) :
    serreQuotientLength P l (P.isoModSerre.Q.obj X) = l X := rfl

include hi ha hz in
/-- 商の評価は代表元の違いによらず同型で不変である。 -/
lemma serreQuotientLength_iso {X Y : P.isoModSerre.Localization} (e : X ≅ Y) :
    serreQuotientLength P l X = serreQuotientLength P l Y := by
  obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv P.isoModSerre).surjective X
  obtain ⟨Y, rfl⟩ := (Localization.Construction.objEquiv P.isoModSerre).surjective Y
  exact additiveLength_eq_of_localization_iso P l hi ha hz e

include hi ha hz in
/-- 商の短完全列は、単射とその余核の持ち上げによって加法性を満たす。 -/
lemma serreQuotientLength_add {S : ShortComplex P.isoModSerre.Localization}
    (hS : S.ShortExact) :
    serreQuotientLength P l S.X₂ = serreQuotientLength P l S.X₁ +
      serreQuotientLength P l S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits P.isoModSerre.Q P
  obtain ⟨X, Y, f, hf, ⟨e⟩⟩ :=
    (ObjectProperty.SerreClassLocalization.mono_iff P.isoModSerre.Q P S.f).mp inferInstance
  let e₁ : P.isoModSerre.Q.obj X ≅ S.X₁ := Arrow.leftFunc.mapIso e
  let e₂ : P.isoModSerre.Q.obj Y ≅ S.X₂ := Arrow.rightFunc.mapIso e
  let e₃ : P.isoModSerre.Q.obj (cokernel f) ≅ S.X₃ :=
    PreservesCokernel.iso P.isoModSerre.Q f ≪≫
      cokernel.mapIso (P.isoModSerre.Q.map f) S.f e₁ e₂ (Arrow.w e.hom).symm ≪≫
      IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel
  rw [← serreQuotientLength_iso P l hi ha hz e₁,
    ← serreQuotientLength_iso P l hi ha hz e₂,
    ← serreQuotientLength_iso P l hi ha hz e₃]
  exact ha (show (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact from
    { exact := ShortComplex.exact_cokernel f })

/-- 零長さの対象をちょうど殺す商では、長さが零であることと零対象が同値。 -/
lemma serreQuotientLength_eq_zero_iff (hP : ∀ X, l X = 0 ↔ P X)
    (X : P.isoModSerre.Localization) : serreQuotientLength P l X = 0 ↔ IsZero X := by
  obtain ⟨M, rfl⟩ := (Localization.Construction.objEquiv P.isoModSerre).surjective X
  exact (hP M).trans
    (ObjectProperty.SerreClassLocalization.isZero_obj_iff P.isoModSerre.Q P M).symm

end SerrePositivity

end SerreLengthPart

section AdditiveLengthPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {L : Type*} [AddCommMonoid L] [PartialOrder L] [IsOrderedAddMonoid L]
  {C : Type*} [Category* C] [Abelian C] (l : C → L)
  (ha : ∀ {S : ShortComplex C}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)
  (hn : ∀ X, 0 ≤ l X)

include ha hn in
/-- 単射に沿う長さの単調性。 -/
lemma additiveLength_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : l X ≤ l Y := by
  have h := ha (show (ShortComplex.mk f (cokernel.π f)
    (cokernel.condition f)).ShortExact from { exact := ShortComplex.exact_cokernel f })
  change l Y = l X + l (cokernel f) at h
  rw [h]
  exact le_add_of_nonneg_right (hn _)

include ha hn in
/-- 全射に沿う長さの単調性。 -/
lemma additiveLength_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : l Y ≤ l X := by
  have h := ha (show (ShortComplex.mk (kernel.ι f) f
    (kernel.condition f)).ShortExact from { exact := ShortComplex.exact_kernel f })
  change l X = l (kernel f) + l Y at h
  rw [h]
  exact le_add_of_nonneg_left (hn _)

include ha hn in
/-- 直和因子の長さは元の対象の長さ以下。 -/
lemma additiveLength_le_of_retract {X Y : C} (r : Retract X Y) : l X ≤ l Y :=
  additiveLength_le_of_mono l ha hn r.i

/-- 零長さの対象。 -/
def zeroAdditiveLength : ObjectProperty C := fun X ↦ l X = 0

include ha hn in
/-- 非負で短完全列に加法的な長さの零対象は Serre 部分圏をなす。 -/
lemma zeroAdditiveLength_isSerreClass (hz : l 0 = 0) :
    (zeroAdditiveLength l).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, hz⟩
  prop_of_mono f _ hY := le_antisymm
    ((additiveLength_le_of_mono l ha hn f).trans_eq hY) (hn _)
  prop_of_epi f _ hX := le_antisymm
    ((additiveLength_le_of_epi l ha hn f).trans_eq hX) (hn _)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    change l _ = 0
    rw [ha hS, h₁, h₃, add_zero]

end SerrePositivity

end AdditiveLengthPart
