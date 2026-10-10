module

public import SerrePositivity.CategoryTheory.BoundedTStructureIdempotent
public import SerrePositivity.CategoryTheory.TExactTruncation
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-!
# 切り詰めと両立する局所化上の t 構造

右分数表示をもつ三角的局所化について、非正切り詰めが分母を局所化後の同型へ
送るならば、元の t 構造の本質像が局所化上の t 構造を定める。
分数の分母を切り詰めたものと置き換えることで、商上の直交性を証明する。
有界性と冪等完備性も降下する。

切り詰めた分母の可逆性は明示的な仮定であり、このファイルで Serre 条件から
導いたことにはしない。Verdier 商の対象を具体化する際に検証すべき接続である。
-/

@[expose] public section

universe v u v' u'

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
