module

public import SerrePositivity.CategoryTheory.VerdierTStructure
public import SerrePositivity.CategoryTheory.TExactTruncation
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# t 完全な三角関手の核による Verdier 商

核の分母条件を、関手による射の可逆性から証明する。
切り詰めた分母の条件を独立の入力として要求しない。
-/

@[expose] public section

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
