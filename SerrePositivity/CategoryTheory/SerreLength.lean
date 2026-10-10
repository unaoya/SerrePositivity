module

public import SerrePositivity.CategoryTheory.SerreSubcategory
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Basic.Real.Basic

/-!
# Serre 商への加法的な対象評価の降下

同型で不変、短完全列で加法的な可換加法モノイド値の対象評価が Serre 部分圏で零ならば、
商で新しく生じる同型にも不変である。核・余核の公式と分数表示を使う。
-/

@[expose] public section

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
