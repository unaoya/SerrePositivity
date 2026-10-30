module

public import SerrePositivity.CategoryTheory.TStructure.Bounded
public import SerrePositivity.CategoryTheory.TStructure.Basic
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # 局所化・Verdier 商・核による商の上の t 構造

## 概要

切り詰めと両立する局所化の上に t 構造が誘導されること、分母が切り詰め条件を満たす Verdier 商の t 構造、t 完全な三角関手の核による Verdier 商の t 構造、t 構造と両立するホモロジー関手の核による商を与える。

## 方針

一般の局所化の版（`localizationTStructure`）を示し、Verdier 商・核による商はその特殊化として導く。

## 規約

Mathlib の `TStructure.onBounded`・`HasInducedTStructure` とは補い合う関係（重複ではない）。

## 使われ方

Asymptotic の階数の商の t 構造。
-/

@[expose] public noncomputable section

universe v u v' u'

section LocalizationTStructurePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasRightCalculusOfFractions] [L.CommShift ℤ] [L.IsTriangulated]
  (hτ : W.IsInvertedBy (t.truncLE 0 ⋙ L))

include hτ in
/-- 切り詰めた分母の可逆性から、局所化後の非正対象と正対象の直交性を得る。 -/
lemma localization_hom_eq_zero {X Y : C} [t.IsLE X 0] [t.IsGE Y 1]
    (f : L.obj X ⟶ L.obj Y) : f = 0 := by
  obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction L W f
  have : IsIso (L.map ((t.truncLE 0).map φ.s)) := hτ φ.s φ.hs
  have hden : IsIso (L.map ((t.truncLEι 0).app φ.X' ≫ φ.s)) := by
    have hs : (t.truncLEι 0).app φ.X' ≫ φ.s =
        (t.truncLE 0).map φ.s ≫ (t.truncLEι 0).app X := by
      simp
    rw [hs, L.map_comp]
    infer_instance
  rw [← cancel_epi (L.map ((t.truncLEι 0).app φ.X' ≫ φ.s)), comp_zero,
    L.map_comp, assoc, φ.map_s_comp_map, ← L.map_comp]
  rw [t.zero ((t.truncLEι 0).app φ.X' ≫ φ.f) 0 1, L.map_zero]

set_option backward.defeqAttrib.useBackward true in
/-- 切り詰めた分母が可逆になる三角的局所化上の t 構造。 -/
noncomputable def localizationTStructure : TStructure D where
  le n := (t.le n).map L
  ge n := (t.ge n).map L
  le_shift n a n' h X hX := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := hX
    exact ⟨Y⟦a⟧, t.le_shift n a n' h Y hY,
      ⟨(L.commShiftIso a).app Y ≪≫ (shiftFunctor D a).mapIso e⟩⟩
  ge_shift n a n' h X hX := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := hX
    exact ⟨Y⟦a⟧, t.ge_shift n a n' h Y hY,
      ⟨(L.commShiftIso a).app Y ≪≫ (shiftFunctor D a).mapIso e⟩⟩
  zero' {X Y} f hX hY := by
    obtain ⟨X', hX', ⟨eX⟩⟩ := hX
    obtain ⟨Y', hY', ⟨eY⟩⟩ := hY
    have : t.IsLE X' 0 := ⟨hX'⟩
    have : t.IsGE Y' 1 := ⟨hY'⟩
    have h := localization_hom_eq_zero t L W hτ (eX.hom ≫ f ≫ eY.inv)
    simpa using congrArg (fun g ↦ eX.inv ≫ g ≫ eY.hom) h
  le_zero_le := ObjectProperty.map_monotone t.le_zero_le L
  ge_one_le := ObjectProperty.map_monotone t.ge_one_le L
  exists_triangle_zero_one X := by
    have := Localization.essSurj L W
    let X' := L.objPreimage X
    let e := L.objObjPreimageIso X
    obtain ⟨A, B, hA, hB, f, g, δ, hT⟩ := t.exists_triangle_zero_one X'
    refine ⟨L.obj A, L.obj B, (t.le 0).prop_map_obj L hA,
      (t.ge 1).prop_map_obj L hB, L.map f ≫ e.hom, e.inv ≫ L.map g,
      L.map δ ≫ (L.commShiftIso (1 : ℤ)).hom.app A, ?_⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _))

/-- 元の圏の次数上界は、構成した局所化上の t 構造でも保たれる。 -/
lemma localizationTStructure_isLE_obj (X : C) (n : ℤ) [t.IsLE X n] :
    (localizationTStructure t L W hτ).IsLE (L.obj X) n :=
  ⟨(t.le n).prop_map_obj L (t.le_of_isLE X n)⟩

/-- 元の圏の次数下界は、構成した局所化上の t 構造でも保たれる。 -/
lemma localizationTStructure_isGE_obj (X : C) (n : ℤ) [t.IsGE X n] :
    (localizationTStructure t L W hτ).IsGE (L.obj X) n :=
  ⟨(t.ge n).prop_map_obj L (t.ge_of_isGE X n)⟩

/-- 局所化関手は構成した t 構造に関して t 完全である。 -/
lemma localizationTStructure_tExact : L.TExact t (localizationTStructure t L W hτ) := by
  have : L.RightTExact t (localizationTStructure t L W hτ) :=
    Functor.RightTExact.mk _ _ _ (fun X _ ↦ localizationTStructure_isLE_obj t L W hτ X 0)
  have : L.LeftTExact t (localizationTStructure t L W hτ) :=
    Functor.LeftTExact.mk _ _ _ (fun X _ ↦ localizationTStructure_isGE_obj t L W hτ X 0)
  exact ⟨inferInstance, inferInstance⟩

/-- 元の圏の全対象が有界ならば、局所化後の全対象も有界である。 -/
lemma localizationTStructure_bounded (hb : ∀ X : C, t.bounded X) (Y : D) :
    (localizationTStructure t L W hτ).bounded Y := by
  have := Localization.essSurj L W
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb (L.objPreimage Y)
  have hge := localizationTStructure_isGE_obj t L W hτ (L.objPreimage Y) a
  have hle := localizationTStructure_isLE_obj t L W hτ (L.objPreimage Y) b
  exact ⟨⟨a, (localizationTStructure t L W hτ).isGE_of_iso (L.objObjPreimageIso Y) a⟩,
    ⟨b, (localizationTStructure t L W hτ).isLE_of_iso (L.objObjPreimageIso Y) b⟩⟩

include L W hτ in
/-- 有界性と分母の切り詰め条件を満たす局所化は、既に冪等完備である。 -/
lemma localization_isIdempotentComplete [IsTriangulated D] (hb : ∀ X : C, t.bounded X) :
    IsIdempotentComplete D :=
  isIdempotentComplete_of_bounded_tStructure (localizationTStructure t L W hτ)
    (localizationTStructure_bounded t L W hτ hb)

/-- 分母の非正切り詰めが可逆になることは、t 完全な局所化 t 構造の存在と同値。 -/
lemma exists_tExact_localizationTStructure_iff :
    (∃ s : TStructure D, L.TExact t s) ↔ W.IsInvertedBy (t.truncLE 0 ⋙ L) := by
  constructor
  · rintro ⟨s, hs⟩ X Y f hf
    have := Localization.inverts L W f hf
    exact tExact_isIso_map_truncLE t s L f 0
  · intro h
    exact ⟨localizationTStructure t L W h, localizationTStructure_tExact t L W h⟩

end SerrePositivity

end LocalizationTStructurePart

section VerdierTStructurePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C) (P : ObjectProperty C) [P.IsTriangulated]
  (hτ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P.trW f → P.trW ((t.truncLE 0).map f))

include hτ in
omit [IsTriangulated C] [P.IsTriangulated] in
/-- 非正切り詰めが分母を保つならば、切り詰めた分母は Verdier 商で可逆になる。 -/
lemma verdier_truncLE_inverts : P.trW.IsInvertedBy (t.truncLE 0 ⋙ P.trW.Q) :=
  fun _ _ f hf ↦ Localization.inverts P.trW.Q P.trW _ (hτ f hf)

/-- 分母の切り詰め条件を満たす Verdier 商上の t 構造。 -/
noncomputable def verdierTStructure : TStructure P.trW.Localization :=
  localizationTStructure t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ)

/-- Verdier 商の非正側は、元の非正側の本質像である。 -/
lemma verdierTStructure_le (n : ℤ) :
    (verdierTStructure t P hτ).le n = (t.le n).map P.trW.Q := rfl

/-- Verdier 商の非負側は、元の非負側の本質像である。 -/
lemma verdierTStructure_ge (n : ℤ) :
    (verdierTStructure t P hτ).ge n = (t.ge n).map P.trW.Q := rfl

/-- 標準的な Verdier 商関手は構成した t 構造に関して t 完全である。 -/
lemma verdierTStructure_tExact : P.trW.Q.TExact t (verdierTStructure t P hτ) :=
  localizationTStructure_tExact t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ)

/-- 元の t 構造が有界ならば、Verdier 商上の t 構造も有界である。 -/
lemma verdierTStructure_bounded (hb : ∀ X : C, t.bounded X) (Y : P.trW.Localization) :
    (verdierTStructure t P hτ).bounded Y :=
  localizationTStructure_bounded t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ) hb Y

include hτ in
/-- 有界性と分母の切り詰め条件を満たす Verdier 商は冪等完備である。 -/
lemma verdier_isIdempotentComplete (hb : ∀ X : C, t.bounded X) :
    IsIdempotentComplete P.trW.Localization :=
  localization_isIdempotentComplete t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ) hb

/-- 条件を満たす有界 Verdier 商と、その冪等完備化の同値。 -/
noncomputable def verdierKaroubiEquivalence (hb : ∀ X : C, t.bounded X) :
    P.trW.Localization ≌ Karoubi P.trW.Localization := by
  have := verdier_isIdempotentComplete t P hτ hb
  exact toKaroubiEquivalence P.trW.Localization

include hτ in
/-- 冪等完備化した商の任意の対象は、元の圏の実際の対象の像に同型である。 -/
lemma verdierKaroubi_has_representative (hb : ∀ X : C, t.bounded X)
    (Y : Karoubi P.trW.Localization) :
    ∃ X : C, Nonempty ((toKaroubi P.trW.Localization).obj (P.trW.Q.obj X) ≅ Y) := by
  have := verdier_isIdempotentComplete t P hτ hb
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (toKaroubi P.trW.Localization) Y
  have := Localization.essSurj P.trW.Q P.trW
  exact ⟨P.trW.Q.objPreimage Z,
    ⟨(toKaroubi P.trW.Localization).mapIso (P.trW.Q.objObjPreimageIso Z) ≪≫ e⟩⟩

end SerrePositivity

end VerdierTStructurePart

section TExactKernelQuotientPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Idempotents
open scoped ZeroObject

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- 三角関手で零になる対象の部分圏。 -/
def triangulatedKernel : ObjectProperty C := fun X ↦ IsZero (F.obj X)

instance : (triangulatedKernel F).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso (F.mapIso e.symm)

instance : (triangulatedKernel F).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, F.map_isZero (isZero_zero C)⟩
  toIsStableUnderShift := ⟨fun n ↦ ⟨fun X h ↦
    ((shiftFunctor D n).map_isZero h).of_iso ((F.commShiftIso n).app X)⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    Triangle.isZero₂_of_isZero₁₃ _ (F.map_distinguished T hT) h₁ h₃)

/-- 核を錐にもつ射は、ちょうど関手によって可逆になる射。 -/
lemma triangulatedKernel_trW_iff {X Y : C} (f : X ⟶ Y) :
    (triangulatedKernel F).trW f ↔ IsIso (F.map f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  exact ((triangulatedKernel F).trW_iff_of_distinguished _ hT).trans
    (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT))

variable (t : TStructure C) (s : TStructure D) [F.TExact t s]

include s in
/-- t 完全性から、核の分母が任意の非正切り詰めで保たれる。 -/
lemma triangulatedKernel_truncLE {X Y : C} (f : X ⟶ Y)
    (hf : (triangulatedKernel F).trW f) (n : ℤ) :
    (triangulatedKernel F).trW ((t.truncLE n).map f) := by
  have := (triangulatedKernel_trW_iff F f).1 hf
  exact (triangulatedKernel_trW_iff F _).2 (tExact_isIso_map_truncLE t s F f n)

variable [IsTriangulated C]

/-- t 完全な三角関手の核による商に入る t 構造。 -/
noncomputable def kernelQuotientTStructure :
    TStructure (triangulatedKernel F).trW.Localization :=
  verdierTStructure t (triangulatedKernel F)
    (fun _ _ f hf ↦ triangulatedKernel_truncLE F t s f hf 0)

/-- 核による標準商関手は、構成した t 構造に関して t 完全。 -/
lemma kernelQuotient_tExact :
    (triangulatedKernel F).trW.Q.TExact t (kernelQuotientTStructure F t s) :=
  verdierTStructure_tExact t _ _

/-- 元の t 構造が有界なら、核による商も有界。 -/
lemma kernelQuotientTStructure_bounded (hb : ∀ X : C, t.bounded X)
    (Y : (triangulatedKernel F).trW.Localization) :
    (kernelQuotientTStructure F t s).bounded Y :=
  verdierTStructure_bounded t _ _ hb Y

include s in
/-- 有界 t 構造をもつ圏からの t 完全関手の核による商は冪等完備。 -/
lemma kernelQuotient_isIdempotentComplete (hb : ∀ X : C, t.bounded X) :
    IsIdempotentComplete (triangulatedKernel F).trW.Localization :=
  verdier_isIdempotentComplete t _
    (fun _ _ f hf ↦ triangulatedKernel_truncLE F t s f hf 0) hb

include s in
/-- 商の冪等完備化の対象は、元の圏の対象で表せる。 -/
lemma kernelQuotientKaroubi_has_representative (hb : ∀ X : C, t.bounded X)
    (Y : Karoubi (triangulatedKernel F).trW.Localization) :
    ∃ X : C, Nonempty ((toKaroubi _).obj ((triangulatedKernel F).trW.Q.obj X) ≅ Y) :=
  verdierKaroubi_has_representative t _
    (fun _ _ f hf ↦ triangulatedKernel_truncLE F t s f hf 0) hb Y

/-- 誘導された t 構造に関して、三角部分圏の包含は t 完全。 -/
instance inducedTStructure_inclusion_tExact (P : ObjectProperty C)
    [P.IsTriangulated] [P.HasInducedTStructure t] : P.ι.TExact (P.tStructure t) t where
  rightTExact := Functor.RightTExact.mk _ _ _ (fun X hX ↦
    (P.tStructure_isLE_iff t X 0).1 hX)
  leftTExact := Functor.LeftTExact.mk _ _ _ (fun X hX ↦
    (P.tStructure_isGE_iff t X 0).1 hX)

/-- 有界部分圏上の誘導 t 構造は有界。 -/
lemma onBounded_bounded (X : t.bounded.FullSubcategory) : t.onBounded.bounded X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
  exact ⟨⟨a, (t.bounded.tStructure_isGE_iff t X a).2 ha⟩,
    ⟨b, (t.bounded.tStructure_isLE_iff t X b).2 hb⟩⟩

end SerrePositivity

end TExactKernelQuotientPart

section HomologicalKernelTStructurePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (F : C ⥤ A) [F.IsHomological]

/-- ホモロジー関手をシフトと合成してもホモロジー関手である。 -/
instance homological_shift_comp (q : ℤ) : (shiftFunctor C q ⋙ F).IsHomological where
  exact T hT := by
    let := Functor.ShiftSequence.tautological F ℤ
    exact F.homologySequence_exact₂ T hT q

/-- 錐とその逆シフトの像が零なら、ホモロジー関手は第一の射を同型にする。 -/
lemma homological_isIso_map_of_cone_zeros (T : Triangle C) (hT : T ∈ distTriang C)
    (h₀ : IsZero (F.obj T.obj₃)) (hprev : IsZero (F.obj (T.obj₃⟦(-1 : ℤ)⟧))) :
    IsIso (F.map T.mor₁) := by
  have : Epi (F.map T.mor₁) :=
    (F.map_distinguished_exact T hT).epi_f (h₀.eq_of_tgt _ _)
  have : Mono (F.map T.mor₁) :=
    (F.map_distinguished_exact _ (inv_rot_of_distTriang T hT)).mono_g (hprev.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

variable (t : TStructure C)
  (hneg : ∀ (X : C), t.IsLE X (-1) → IsZero (F.obj X))
  (hpos : ∀ (X : C), t.IsGE X 1 → IsZero (F.obj X))

include hpos in
/-- 切り詰め境界の内側では、包含射はシフトした第零ホモロジーで同型になる。 -/
lemma homological_truncLEι_isIso (X : C) (q : ℤ) (hq : q ≤ 0) :
    IsIso ((shiftFunctor C q ⋙ F).map ((t.truncLEι 0).app X)) := by
  apply homological_isIso_map_of_cone_zeros (shiftFunctor C q ⋙ F)
    _ (t.triangleLEGE_distinguished 0 1 rfl X)
  · change IsZero (F.obj (((t.truncGE 1).obj X)⟦q⟧))
    apply hpos
    have := t.isGE_shift ((t.truncGE 1).obj X) 1 q (1 - q) (by omega)
    exact t.isGE_of_ge _ 1 (1 - q) (by omega)
  · change IsZero (F.obj ((((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧)⟦q⟧))
    apply hpos
    have := t.isGE_shift ((t.truncGE 1).obj X) 1 (-1) 2 (by omega)
    have := t.isGE_shift (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧) 2 q (2 - q) (by omega)
    exact t.isGE_of_ge _ 1 (2 - q) (by omega)

include hneg in
omit [Abelian A] [F.IsHomological] in
/-- 境界の外側では、切り詰めた対象のホモロジーは零になる。 -/
lemma homological_truncLE_isZero (X : C) (q : ℤ) (hq : 0 < q) :
    IsZero ((shiftFunctor C q ⋙ F).obj ((t.truncLE 0).obj X)) := by
  apply hneg
  have := t.isLE_shift ((t.truncLE 0).obj X) 0 q (-q) (by omega)
  exact t.isLE_of_le _ (-q) (-1) (by omega)

include hneg hpos in
/-- 全シフトのホモロジーの核の分母は、非正切り詰めで保たれる。 -/
theorem homologicalKernel_truncLE {X Y : C} (f : X ⟶ Y)
    (hf : F.homologicalKernel.trW f) :
    F.homologicalKernel.trW ((t.truncLE 0).map f) := by
  let := Functor.ShiftSequence.tautological F ℤ
  rw [F.mem_homologicalKernel_trW_iff] at hf ⊢
  intro q
  change IsIso ((shiftFunctor C q ⋙ F).map ((t.truncLE 0).map f))
  let G := shiftFunctor C q ⋙ F
  by_cases hq : q ≤ 0
  · have : IsIso (G.map f) := hf q
    have := homological_truncLEι_isIso F t hpos X q hq
    have := homological_truncLEι_isIso F t hpos Y q hq
    have he : G.map ((t.truncLE 0).map f) =
        G.map ((t.truncLEι 0).app X) ≫ G.map f ≫ inv (G.map ((t.truncLEι 0).app Y)) := by
      rw [← cancel_mono (G.map ((t.truncLEι 0).app Y))]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← G.map_comp]
      rw [(t.truncLEι 0).naturality f]
      rfl
    rw [he]
    infer_instance
  · exact (homological_truncLE_isZero F t hneg X q (by omega)).isIso
      (homological_truncLE_isZero F t hneg Y q (by omega)) _

end SerrePositivity

end HomologicalKernelTStructurePart
