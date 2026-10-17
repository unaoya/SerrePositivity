module
public import SerrePositivity.DifferentialGraded.Verdier.TriangulatedHomComparison
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # 厚い帰納に使う、指定始域からの Hom 比較の閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated Preadditive
open scoped ZeroObject
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
  [HasShift C ℤ] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated C] [Pretriangulated T]
  (F : C ⥤ T) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]

/-- U17 の Hom 比較の五項完全列の議論を、指定した一つの始域へ局所化する。 -/
lemma criterionPerfHomComparison_triangle (X : C) (t : Triangle C) (ht : t ∈ distTriang C)
    (h₁ : Function.Bijective (F.map (X := X) (Y := t.obj₁)))
    (h₃ : Function.Bijective (F.map (X := X) (Y := t.obj₃)))
    (h₁s : Function.Bijective (F.map (X := X) (Y := t.obj₁⟦(1 : ℤ)⟧)))
    (h₃s : Function.Bijective (F.map (X := X) (Y := t.obj₃⟦(-1 : ℤ)⟧))) :
    Function.Bijective (F.map (X := X) (Y := t.obj₂)) := by
  have hker : ∀ f : X ⟶ t.obj₂, F.map f = 0 → f = 0 := by
    intro f hf
    have hz : f ≫ t.mor₂ = 0 := h₃.1 (by
      rw [Functor.map_comp, hf, zero_comp, Functor.map_zero])
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ t ht f hz
    have haz : F.map a ≫ (F.mapTriangle.obj t.invRotate).mor₂ = 0 := by
      change F.map a ≫ F.map t.mor₁ = 0
      rw [← Functor.map_comp, ← ha, hf]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t.invRotate)
      (F.map_distinguished _ (inv_rot_of_distTriang _ ht)) (F.map a) haz
    obtain ⟨c, hc⟩ := h₃s.2 b
    have hac : a = c ≫ t.invRotate.mor₁ := h₁.1 (by
      rw [Functor.map_comp, hc]
      exact hb)
    rw [ha, hac, Category.assoc]
    have hi : t.invRotate.mor₁ ≫ t.mor₁ = 0 :=
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ ht)
    rw [hi, comp_zero]
  constructor
  · intro f g hfg
    have hz : F.map (f - g) = 0 := by rw [Functor.map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hker (f - g) hz)
  · intro f
    obtain ⟨c, hc⟩ := h₃.2 (f ≫ F.map t.mor₂)
    have hz : c ≫ t.mor₃ = 0 := h₁s.1 (by
      rw [Functor.map_comp, hc, Category.assoc, ← Functor.map_comp,
        comp_distTriang_mor_zero₂₃ _ ht, Functor.map_zero, comp_zero]
      exact (F.map_zero _ _).symm)
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ t ht c hz
    have hdiff : (f - F.map d) ≫ (F.mapTriangle.obj t).mor₂ = 0 := by
      change (f - F.map d) ≫ F.map t.mor₂ = 0
      rw [sub_comp, ← Functor.map_comp, ← hd, hc, sub_self]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t)
      (F.map_distinguished _ ht) (f - F.map d) hdiff
    obtain ⟨a, ha⟩ := h₁.2 b
    refine ⟨d + a ≫ t.mor₁, ?_⟩
    rw [Functor.map_add, Functor.map_comp, ha]
    have hb' : f - F.map d = b ≫ F.map t.mor₁ := hb
    rw [← hb']
    abel

/-- 指定した始域の族に関する全単射性。 -/
def criterionPerfRelativeHomTargets (S : ObjectProperty C) : ObjectProperty C :=
  fun Y => ∀ X, S X → Function.Bijective (F.map (X := X) (Y := Y))

variable (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsStableUnderShift ℤ]

instance criterionPerfRelativeHomTargetsClosedUnderIso :
    (criterionPerfRelativeHomTargets F S).IsClosedUnderIsomorphisms where
  of_iso e h X hX := homComparison_bijective_of_iso F (Iso.refl X) e (h X hX)

instance criterionPerfRelativeHomTargetsShift :
    (criterionPerfRelativeHomTargets F S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y h X hX => by
    let X' := (shiftFunctor C n).objPreimage X
    have hX' : S X' := (S.prop_shift_iff_of_isStableUnderShift X' n).1
      (S.prop_of_iso ((shiftFunctor C n).objObjPreimageIso X).symm hX)
    exact homComparison_bijective_of_iso F ((shiftFunctor C n).objObjPreimageIso X)
      (Iso.refl (Y⟦n⟧)) (homComparison_bijective_shift_both F (h X' hX') n)⟩

instance criterionPerfRelativeHomTargetsTriangulated :
    (criterionPerfRelativeHomTargets F S).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun X _ => by
    constructor
    · intro f g _
      exact (isZero_zero C).eq_of_tgt f g
    · intro f
      exact ⟨0, (F.map_isZero (isZero_zero C)).eq_of_tgt _ _⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun t ht h₁ h₃ X hX =>
    criterionPerfHomComparison_triangle F X t ht (h₁ X hX) (h₃ X hX)
      ((criterionPerfRelativeHomTargets F S).le_shift (1 : ℤ) _ h₁ X hX)
      ((criterionPerfRelativeHomTargets F S).le_shift (-1 : ℤ) _ h₃ X hX))

instance criterionPerfRelativeHomTargetsRetracts :
    (criterionPerfRelativeHomTargets F S).IsStableUnderRetracts where
  of_retract a h X hX := by
    constructor
    · intro f g hfg
      have he : f ≫ a.i = g ≫ a.i := (h X hX).1 (by
        rw [F.map_comp, F.map_comp, hfg])
      have := congrArg (fun k => k ≫ a.r) he
      simpa only [Category.assoc, a.retract, Category.comp_id] using this
    · intro g
      obtain ⟨f, hf⟩ := (h X hX).2 (g ≫ F.map a.i)
      refine ⟨f ≫ a.r, ?_⟩
      rw [F.map_comp, hf, Category.assoc, ← F.map_comp, a.retract, F.map_id,
        Category.comp_id]

omit [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
    [HasShift C ℤ] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated C] [Pretriangulated T] [F.CommShift ℤ] [F.IsTriangulated] [F.Additive] in
/-- 反対圏を使って同じ帰納を始域にも適用するための全単射性の移送。 -/
lemma criterionPerfHomComparison_op_iff (X Y : C) :
    Function.Bijective (F.op.map (X := Opposite.op Y) (Y := Opposite.op X)) ↔
      Function.Bijective (F.map (X := X) (Y := Y)) := by
  constructor
  · intro h
    constructor
    · intro f g he
      exact congrArg Quiver.Hom.unop (h.1 (congrArg Quiver.Hom.op he))
    · intro f
      obtain ⟨g, hg⟩ := h.2 f.op
      exact ⟨g.unop, congrArg Quiver.Hom.unop hg⟩
  · intro h
    constructor
    · intro f g he
      exact congrArg Quiver.Hom.op (h.1 (congrArg Quiver.Hom.unop he))
    · intro f
      obtain ⟨g, hg⟩ := h.2 f.unop
      exact ⟨g.op, congrArg Quiver.Hom.op hg⟩

end SerrePositivity.DifferentialGraded.Morita
