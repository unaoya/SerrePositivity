module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-! # t 構造の heart・retract・切り詰め

## 概要

t 構造の heart がアーベル圏であること（零対象・有限積・冪等完備性を含む）、t 構造の次数範囲が retract で閉じること、t 完全な関手と切り詰めた射の可逆性を与える。

## 方針

heart のアーベル性は Mathlib の `AbelianSubcategory.abelian`・`admissibleMorphism` に乗せる。retract での安定性は切り詰めの関手性から。

## 規約

Mathlib には heart のアーベル性・`ContainsZero`・有限積のインスタンスがない（提出候補）。

## 使われ方

有界 t 構造（`TStructure/Bounded`）、局所化上の t 構造、Asymptotic の t 構造。
-/

@[expose] public noncomputable section

universe v u v' u'

section TStructureHeartPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)
  {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]

/-- heart は零対象を含む。 -/
instance heart_containsZero : t.heart.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, t.le_of_isLE 0 0, t.ge_of_isGE 0 0⟩

/-- heart は周囲の三角圏における二項積で閉じている。 -/
instance heart_closedUnderBinaryProducts : t.heart.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have h₁ := p.prop_diag_obj (.mk .left)
    have h₃ := p.prop_diag_obj (.mk .right)
    refine t.heart.prop_of_iso (X :=
      (p.diag.obj (.mk .left)) ⨯ (p.diag.obj (.mk .right))) ?_ ?_
    · exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)
    · exact ⟨(t.isLE₂ _ (binaryProductTriangle_distinguished _ _) 0
        ⟨h₁.1⟩ ⟨h₃.1⟩).le,
        (t.isGE₂ _ (binaryProductTriangle_distinguished _ _) 0 ⟨h₁.2⟩ ⟨h₃.2⟩).ge⟩

/-- heart は有限積で閉じており、その充満部分圏も有限積をもつ。 -/
instance heart_closedUnderFiniteProducts : t.heart.IsClosedUnderFiniteProducts := .mk'

include t in
/-- heart の任意の完全忠実な表示にも有限積が存在する。 -/
lemma heart_hasFiniteProducts : HasFiniteProducts H := by
  have : HasFiniteProducts (t.ιHeart (H := H)).EssImageSubcategory := by
    change HasFiniteProducts (t.ιHeart (H := H)).essImage.FullSubcategory
    rw [t.essImage_ιHeart H]
    infer_instance
  have : (t.ιHeart (H := H)).toEssImage.Additive :=
    ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
      (t.ιHeart.map_add (f := f) (g := g))⟩
  have : (t.ιHeart (H := H)).toEssImage.asEquivalence.functor.Additive :=
    inferInstanceAs (t.ιHeart (H := H)).toEssImage.Additive
  exact CategoryTheory.Functor.hasFiniteProducts_of_additive_of_essSurj
    (t.ιHeart (H := H)).toEssImage.asEquivalence.inverse

/-- heart の対象間では負の次数のシフトへの射は零である。 -/
lemma heart_hom_shift_neg_eq_zero {X Y : H} {n : ℤ}
    (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) (hn : n < 0) : f = 0 := by
  have := t.isGE_shift (t.ιHeart.obj Y) 0 n (-n) (by omega)
  exact t.zero f 0 (-n) (by omega)

variable [IsTriangulated C]

set_option backward.defeqAttrib.useBackward true in
/-- heart 内の射の錐は、シフトした核と余核を結ぶ三角形をもつ。 -/
lemma heart_admissibleMorphism {X Y : H} (f : X ⟶ Y) :
    AbelianSubcategory.admissibleMorphism t.ιHeart f := by
  intro Z g h hT
  let T := Triangle.mk (t.ιHeart.map f) g h
  have hZle : t.IsLE Z 0 := t.isLE₂ T.rotate (rot_of_distTriang _ hT) 0
    (by dsimp [T]; infer_instance) (by
      have := t.isLE_shift (t.ιHeart.obj X) 0 1 (-1)
      exact t.isLE_of_le ((t.ιHeart.obj X)⟦(1 : ℤ)⟧) (-1) 0)
  have hZge : t.IsGE Z (-1) := t.isGE₂ T.rotate (rot_of_distTriang _ hT) (-1)
    (t.isGE_of_ge (t.ιHeart.obj Y) (-1) 0) (t.isGE_shift (t.ιHeart.obj X) 0 1 (-1))
  let L := (t.truncLE (-1)).obj Z
  let Q := (t.truncGE 0).obj Z
  have hL : t.heart (L⟦(-1 : ℤ)⟧) := by
    constructor
    · exact (t.isLE_shift L (-1) (-1) 0).le
    · exact (t.isGE_shift L (-1) (-1) 0).ge
  have hQ : t.heart Q := ⟨t.le_of_isLE Q 0, t.ge_of_isGE Q 0⟩
  rw [← t.essImage_ιHeart H] at hL hQ
  obtain ⟨K, ⟨eK⟩⟩ := hL
  obtain ⟨Q', ⟨eQ⟩⟩ := hQ
  let e : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ L :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫
      (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by omega)).app L
  refine ⟨K, Q', e.hom ≫ (t.truncLEι (-1)).app Z,
    (t.truncGEπ 0).app Z ≫ eQ.inv,
    eQ.hom ≫ (t.truncGEδLE (-1) 0 (by omega)).app Z ≫ e.inv⟦(1 : ℤ)⟧', ?_⟩
  exact isomorphic_distinguished _ (t.triangleLEGE_distinguished (-1) 0 (by omega) Z)
    _ (Triangle.isoMk _ _ e (Iso.refl _) eQ (by simp) (by simp) (by
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id]
      rw [CategoryTheory.Functor.map_id, Category.comp_id]))

/-- heart 内のすべての射がアーベル部分圏の構成条件を満たす。 -/
lemma heart_admissibleMorphism_eq_top :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X Y f
  exact iff_true_intro (heart_admissibleMorphism t f)

/-- heart の任意の表示に、t 構造からアーベル圏構造を与える。 -/
@[instance_reducible]
noncomputable def heartAbelian : Abelian H := by
  have := heart_hasFiniteProducts (H := H) t
  exact AbelianSubcategory.abelian t.ιHeart
    (fun {_ _ _} f hn ↦ heart_hom_shift_neg_eq_zero t f hn)
    (heart_admissibleMorphism_eq_top t)

include t in
/-- heart の任意の表示ではすべての冪等元が分裂する。 -/
lemma heart_isIdempotentComplete : IsIdempotentComplete H := by
  let := heartAbelian (H := H) t
  infer_instance

/-- heart を充満部分圏として取ると、追加の仮定なしにアーベル圏となる。 -/
@[instance_reducible]
noncomputable def heartFullSubcategoryAbelian : Abelian t.heart.FullSubcategory := by
  letI := t.hasHeartFullSubcategory
  exact heartAbelian t

/-- heart の充満部分圏ではすべての冪等元が分裂する。 -/
lemma heartFullSubcategory_isIdempotentComplete :
    IsIdempotentComplete t.heart.FullSubcategory := by
  let := heartFullSubcategoryAbelian t
  infer_instance

end SerrePositivity

end TStructureHeartPart

section TStructureRetractsPart

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

end TStructureRetractsPart

section TExactTruncationPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (t : TStructure C) (s : TStructure D) (F : C ⥤ D)
  [F.CommShift ℤ] [F.IsTriangulated] [F.TExact t s]

include s in
set_option backward.defeqAttrib.useBackward true in
/-- t 完全な関手が可逆にする射は、非正切り詰めの後もその関手で可逆になる。 -/
lemma tExact_isIso_map_truncLE {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] (n : ℤ) :
    IsIso (F.map ((t.truncLE n).map f)) := by
  let G := t.triangleLEGE n (n + 1) rfl ⋙ F.mapTriangle
  have hX : G.obj X ∈ distTriang D :=
    F.map_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl X)
  have hY : G.obj Y ∈ distTriang D :=
    F.map_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl Y)
  have hXle : s.IsLE (G.obj X).obj₁ n :=
    Functor.isLE_obj F t s ((t.truncLE n).obj X) n
  have hYle : s.IsLE (G.obj Y).obj₁ n :=
    Functor.isLE_obj F t s ((t.truncLE n).obj Y) n
  have hXge : s.IsGE (G.obj X).obj₃ (n + 1) :=
    Functor.isGE_obj F t s ((t.truncGE (n + 1)).obj X) (n + 1)
  have hYge : s.IsGE (G.obj Y).obj₃ (n + 1) :=
    Functor.isGE_obj F t s ((t.truncGE (n + 1)).obj Y) (n + 1)
  let e₂ : F.obj X ≅ F.obj Y := asIso (F.map f)
  obtain ⟨e, he⟩ := s.triangle_iso_exists hX hY e₂ n (n + 1)
    hXle hXge hYle hYge
  have heq : G.map f = e.hom := s.triangle_map_ext hX hY n (n + 1) hXle hYge
    (by simpa [G, e₂] using he.symm)
  change IsIso (G.map f).hom₁
  rw [heq]
  infer_instance

end SerrePositivity

end TExactTruncationPart
