module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Karoubi 包絡の線形構造・シフト・完全忠実性・像

## 概要

前加法圏 C の Karoubi 包絡（冪等完備化）について、`Linear` 構造、シフトと標準包含 `toKaroubi` の両立、完全忠実な関手の Karoubi 延長が完全忠実であること、Karoubi 延長の値が冪等元の像であることを示す。

## 方針

どれも Karoubi 包絡の対象 `(X, p)` と射 `f = p ≫ f ≫ p` の成分計算に帰着する。シフトは成分ごとに与え、`toKaroubi` との可換性は定義から。

## 規約

三角構造は `Karoubi/Triangulated`。Mathlib には Karoubi 包絡の `Linear`・シフトはない（提出候補）。

## 使われ方

三角圏の Karoubi 完備化（`Karoubi/Triangulated`）、Verdier 商と完備化の交換（`Triangulated/VerdierKaroubi`）、Asymptotic の支持付き圏の完備化。
-/

@[expose] public noncomputable section

section KaroubiLinearPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents
open CategoryTheory.Functor

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]

instance karoubiHomModule (P Q : Karoubi C) : Module R (P ⟶ Q) where
  smul a f := ⟨a • f.f, by simp only [Linear.comp_smul, Linear.smul_comp, f.comm]⟩
  one_smul f := by ext; exact one_smul R f.f
  mul_smul a b f := by ext; exact mul_smul a b f.f
  smul_zero a := by ext; exact smul_zero a
  smul_add a f g := by ext; exact smul_add a f.f g.f
  add_smul a b f := by ext; exact add_smul a b f.f
  zero_smul f := by ext; exact zero_smul R f.f

instance karoubiLinear : Linear R (Karoubi C) where
  smul_comp _ _ _ a f g := by ext; apply Linear.smul_comp
  comp_smul _ _ _ f a g := by ext; apply Linear.comp_smul

/-- Karoubi 包絡のスカラー作用は元の射への作用そのものである。 -/
@[simp] lemma karoubi_smul_f {P Q : Karoubi C} (a : R) (f : P ⟶ Q) :
    (a • f).f = a • f.f := rfl

instance toKaroubi_linear : (toKaroubi C).Linear R where
  map_smul := by intros; rfl

variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  (F : C ⥤ D)

omit [Linear R C] [Linear R D] in
instance karoubiExtension_additive [F.Additive] :
    ((functorExtension₂ C D).obj F).Additive where
  map_add := by intros; ext; exact F.map_add

instance karoubiExtension_linear [F.Linear R] :
    ((functorExtension₂ C D).obj F).Linear R where
  map_smul := by intros; ext; exact F.map_smul _ _

omit [Linear R C] [Linear R D] in
/-- 冪等完備な値域への延長も加法的である。 -/
instance karoubiExtensionToComplete_additive [IsIdempotentComplete D] [F.Additive] :
    ((functorExtension C D).obj F).Additive := by
  change (((functorExtension₂ C D).obj F) ⋙ (toKaroubiEquivalence D).inverse).Additive
  infer_instance

omit [Preadditive C] [Linear R C] [Preadditive D] [Linear R D] in
/-- 冪等完備な値域への延長は、元の圏上では元の関手に自然同型である。 -/
noncomputable def karoubiExtensionToCompleteFactors [IsIdempotentComplete D] :
    toKaroubi C ⋙ (functorExtension C D).obj F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)
      (toKaroubiEquivalence D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F (toKaroubiEquivalence D).unitIso.symm ≪≫ Functor.rightUnitor F

end SerrePositivity

end KaroubiLinearPart

section KaroubiShiftPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents

variable (C : Type*) [Category* C] [HasShift C ℤ]

/-- シフト関手を各冪等元へ適用して得るシフト。 -/
noncomputable instance karoubiHasShift : HasShift (Karoubi C) ℤ :=
  HasShift.induced (toKaroubi C) ℤ
    (fun n ↦ (functorExtension₂ C C).obj (shiftFunctor C n))
    (fun n ↦ (functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app (shiftFunctor C n))

noncomputable instance toKaroubi_commShift : (toKaroubi C).CommShift ℤ :=
  Functor.CommShift.ofInduced (toKaroubi C) ℤ
    (fun n ↦ (functorExtension₂ C C).obj (shiftFunctor C n))
    (fun n ↦ (functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app (shiftFunctor C n))

@[simp] lemma toKaroubi_commShift_hom_f (X : C) (n : ℤ) :
    (((toKaroubi C).commShiftIso n).hom.app X).f = 𝟙 (X⟦n⟧) := rfl

@[simp] lemma toKaroubi_commShift_inv_f (X : C) (n : ℤ) :
    (((toKaroubi C).commShiftIso n).inv.app X).f = 𝟙 (X⟦n⟧) := rfl

/-- Karoubi シフトの対象は元の対象と冪等元のシフト。 -/
@[simp] lemma karoubi_shift_X (P : Karoubi C) (n : ℤ) :
    (P⟦n⟧).X = P.X⟦n⟧ := rfl

@[simp] lemma karoubi_shift_p (P : Karoubi C) (n : ℤ) :
    (P⟦n⟧).p = P.p⟦n⟧' := rfl

@[simp] lemma karoubi_shift_map_f {P Q : Karoubi C} (f : P ⟶ Q) (n : ℤ) :
    (f⟦n⟧').f = f.f⟦n⟧' := rfl

variable [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]

open CategoryTheory.Limits in
open scoped ZeroObject in
instance karoubiHasZeroObject [HasZeroObject C] : HasZeroObject (Karoubi C) :=
  ⟨⟨(toKaroubi C).obj 0, (toKaroubi C).map_isZero (isZero_zero C)⟩⟩

instance karoubi_shift_additive (n : ℤ) : (shiftFunctor (Karoubi C) n).Additive :=
  inferInstanceAs (((functorExtension₂ C C).obj (shiftFunctor C n)).Additive)

instance karoubi_shift_linear {R : Type*} [Semiring R] [Linear R C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (n : ℤ) :
    (shiftFunctor (Karoubi C) n).Linear R :=
  inferInstanceAs (((functorExtension₂ C C).obj (shiftFunctor C n)).Linear R)

end SerrePositivity

end KaroubiShiftPart

section KaroubiFullyFaithfulPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

instance karoubiExtension_faithful [F.Faithful] :
    ((functorExtension₂ C D).obj F).Faithful where
  map_injective {P Q} f g h := by
    apply Karoubi.hom_ext
    exact F.map_injective (congrArg Karoubi.Hom.f h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance karoubiExtension_full [F.Full] [F.Faithful] :
    ((functorExtension₂ C D).obj F).Full where
  map_surjective {P Q} f := by
    let g := F.preimage f.f
    have hg : P.p ≫ g ≫ Q.p = g := by
      apply F.map_injective
      have h := f.comm
      change F.map P.p ≫ f.f ≫ F.map Q.p = f.f at h
      dsimp only [g]
      rw [F.map_comp, F.map_comp, F.map_preimage]
      exact h
    exact ⟨⟨g, hg⟩, Karoubi.hom_ext _ _ (F.map_preimage f.f)⟩

/-- 形式的直和因子は、元の対象の標準的な像の retract である。 -/
def karoubiRetract (P : Karoubi C) : Retract P ((toKaroubi C).obj P.X) :=
  ⟨P.decompId_i, P.decompId_p, P.decompId.symm⟩

/-- 完全忠実な関手の像の直和因子は、延長した関手の本質像に属する。 -/
theorem karoubiExtension_mem_essImage [F.Full] [F.Faithful]
    (P : Karoubi D) (X : C) (r : Retract P ((toKaroubi D).obj (F.obj X))) :
    ((functorExtension₂ C D).obj F).essImage P := by
  let q : X ⟶ X := F.preimage (r.r.f ≫ r.i.f)
  have hq : F.map q = r.r.f ≫ r.i.f := F.map_preimage _
  have hr : r.i.f ≫ r.r.f = P.p := congrArg Karoubi.Hom.f r.retract
  have hqq : q ≫ q = q := by
    apply F.map_injective
    rw [F.map_comp, hq]
    simp only [Category.assoc, ← Category.assoc r.i.f, hr, Karoubi.p_comp]
  let Q : Karoubi C := ⟨X, q, hqq⟩
  refine ⟨Q, ⟨?_⟩⟩
  refine { hom := ⟨r.r.f, ?_⟩
           inv := ⟨r.i.f, ?_⟩
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · change F.map q ≫ r.r.f ≫ P.p = r.r.f
    rw [hq, Category.assoc, ← Category.assoc r.i.f, hr]
    simp
  · change P.p ≫ r.i.f ≫ F.map q = r.i.f
    rw [hq, ← Category.assoc, ← Category.assoc, Karoubi.p_comp, hr]
    exact Karoubi.p_comp r.i
  · apply Karoubi.hom_ext
    exact hq.symm
  · apply Karoubi.hom_ext
    exact hr

end SerrePositivity

end KaroubiFullyFaithfulPart

section KaroubiImagePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

variable {A : Type*} [Category* A] [Abelian A]

/-- 分裂する冪等元の像は、その直和因子に同型である。 -/
noncomputable def splitIdempotentImageIso {X Y : A} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) : X ≅ Abelian.image (r ≫ i) where
  hom := i ≫ Abelian.factorThruImage (r ≫ i)
  inv := Abelian.image.ι (r ≫ i) ≫ r
  hom_inv_id := by simp only [Category.assoc]; simp [← Category.assoc, h]
  inv_hom_id := by
    apply (cancel_mono (Abelian.image.ι (r ≫ i))).mp
    simp only [Category.assoc, Abelian.image.fac, Category.id_comp]
    have hp : Abelian.image.ι (r ≫ i) ≫ r ≫ i = Abelian.image.ι (r ≫ i) := by
      apply (cancel_epi (Abelian.factorThruImage (r ≫ i))).mp
      simp only [← Category.assoc, Abelian.image.fac]
      simp only [Category.assoc, reassoc_of% h]
    simpa only [Category.assoc, reassoc_of% h, Category.id_comp] using hp

variable {C : Type*} [Category* C] (F : C ⥤ A)

/-- 関手の Karoubi 延長の値は、元の冪等元を送った射の像に同型である。 -/
noncomputable def karoubiExtensionImageIso (P : Karoubi C) :
    ((functorExtension C A).obj F).obj P ≅ Abelian.image (F.map P.p) := by
  let E := (functorExtension C A).obj F
  let e := (karoubiExtensionToCompleteFactors F).app P.X
  let i := E.map P.decompId_i ≫ e.hom
  let r := e.inv ≫ E.map P.decompId_p
  have h : i ≫ r = 𝟙 (E.obj P) := by
    dsimp only [i, r]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← E.map_comp,
      ← P.decompId, CategoryTheory.Functor.map_id]
  have hp : r ≫ i = F.map P.p := by
    dsimp only [i, r]
    rw [Category.assoc, ← Category.assoc (E.map P.decompId_p), ← E.map_comp, ← P.decomp_p]
    have he := (karoubiExtensionToCompleteFactors F).hom.naturality P.p
    change E.map ((toKaroubi C).map P.p) ≫ e.hom = e.hom ≫ F.map P.p at he
    rw [he, Iso.inv_hom_id_assoc]
  have hi := splitIdempotentImageIso i r h
  rw [hp] at hi
  exact hi

end SerrePositivity

end KaroubiImagePart
