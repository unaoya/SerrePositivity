module

public import SerrePositivity.CategoryTheory.TStructureHeart
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# t 構造の次数範囲と冪等分裂

次数の上下界が retract で保たれることと、単一次数に集中した対象の冪等分裂を示す。
後者は有界 t 構造の冪等完備性に向けた振幅帰納法の初期段階になる。
Karoubi 包絡での形式的な直和因子にも、同じ次数に集中する実際の代表対象を与える。
-/

@[expose] public section

universe v u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

/-- t 構造の次数の上界は retract に移る。 -/
lemma tStructure_isLE_of_retract {X Y : C} (r : Retract X Y) (n : ℤ)
    [t.IsLE Y n] : t.IsLE X n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Z f hZ
  have h := t.zero (r.r ≫ f) n (n + 1)
  calc
    f = r.i ≫ (r.r ≫ f) := by simp
    _ = 0 := by rw [h, comp_zero]

/-- t 構造の次数の下界は retract に移る。 -/
lemma tStructure_isGE_of_retract {X Y : C} (r : Retract X Y) (n : ℤ)
    [t.IsGE Y n] : t.IsGE X n := by
  rw [t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro Z f hZ
  have h := t.zero (f ≫ r.i) (n - 1) n
  calc
    f = (f ≫ r.i) ≫ r.r := by simp
    _ = 0 := by rw [h, zero_comp]

/-- 非正側の各次数範囲は retract で閉じている。 -/
instance tStructure_le_stableUnderRetracts (n : ℤ) :
    (t.le n).IsStableUnderRetracts where
  of_retract r h := by
    have : t.IsLE _ n := ⟨h⟩
    exact (tStructure_isLE_of_retract t r n).le

/-- 非負側の各次数範囲は retract で閉じている。 -/
instance tStructure_ge_stableUnderRetracts (n : ℤ) :
    (t.ge n).IsStableUnderRetracts where
  of_retract r h := by
    have : t.IsGE _ n := ⟨h⟩
    exact (tStructure_isGE_of_retract t r n).ge

variable [IsTriangulated C]

/-- heart の対象の冪等元は、周囲の三角圏でも heart の対象を像として分裂する。 -/
lemma heart_idempotent_splits {X : C} (hX : t.heart X) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (Y : C), t.heart Y ∧ ∃ (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = p := by
  have := heartFullSubcategory_isIdempotentComplete t
  let X' : t.heart.FullSubcategory := ⟨X, hX⟩
  let p' : X' ⟶ X' := ⟨p⟩
  have hp' : p' ≫ p' = p' := ObjectProperty.hom_ext _ hp
  obtain ⟨Y, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X' p' hp'
  exact ⟨Y.obj, Y.property, t.heart.ι.map i, t.heart.ι.map r,
    by simpa using t.heart.ι.congr_map hir,
    by simpa [p'] using t.heart.ι.congr_map hri⟩

/-- 単一次数に集中した対象の冪等元は、同じ次数に集中した対象を像として分裂する。 -/
lemma pure_idempotent_splits (X : C) (n : ℤ) [t.IsLE X n] [t.IsGE X n]
    (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : C), t.IsLE Y n ∧ t.IsGE Y n ∧
      ∃ (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = p := by
  have hX : t.heart (X⟦n⟧) :=
    ⟨(t.isLE_shift X n n 0).le, (t.isGE_shift X n n 0).ge⟩
  obtain ⟨Y, hY, i, r, hir, hri⟩ := heart_idempotent_splits t hX ((shiftFunctor C n).map p)
    (by rw [← Functor.map_comp, hp])
  have : t.IsLE Y 0 := ⟨hY.1⟩
  have : t.IsGE Y 0 := ⟨hY.2⟩
  let e : X⟦n⟧⟦-n⟧ ≅ X := (shiftFunctorCompIsoId C n (-n) (by omega)).app X
  refine ⟨Y⟦-n⟧, t.isLE_shift Y 0 (-n) n, t.isGE_shift Y 0 (-n) n,
    i⟦-n⟧' ≫ e.hom, e.inv ≫ r⟦-n⟧', ?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir,
      CategoryTheory.Functor.map_id]
  · rw [Category.assoc, ← Category.assoc _ _ e.hom, ← Functor.map_comp, hri]
    exact shiftFunctorCompIsoId_naturality_1 p n (-n) (by omega)

set_option backward.defeqAttrib.useBackward true in
/-- 単一次数の対象の形式的直和因子は、Karoubi 包絡内で実際の対象の像に同型である。 -/
lemma karoubi_pure_has_representative (P : Karoubi C) (n : ℤ)
    [t.IsLE P.X n] [t.IsGE P.X n] :
    ∃ (Y : C), t.IsLE Y n ∧ t.IsGE Y n ∧ Nonempty ((toKaroubi C).obj Y ≅ P) := by
  obtain ⟨Y, hle, hge, i, r, hir, hri⟩ := pure_idempotent_splits t P.X n P.p P.idem
  refine ⟨Y, hle, hge, ⟨{
    hom := ⟨i, by simp [← hri, ← Category.assoc, hir]⟩
    inv := ⟨r, by simp [← hri, Category.assoc, hir]⟩
    hom_inv_id := by ext; exact hir
    inv_hom_id := by ext; exact hri }⟩⟩

end SerrePositivity
