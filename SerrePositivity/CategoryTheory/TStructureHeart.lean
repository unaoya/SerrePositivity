module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# t 構造の heart のアーベル性

heart 内の射の錐を次数 -1 と 0 で切り詰め、核と余核を与える三角形を作る。
Mathlib の `AbelianSubcategory.abelian` に接続し、heart の冪等完備性を得る。
これは §4 で使う有界 t 構造の一般論の基礎であり、圏全体の冪等完備性や
Verdier 商への t 構造の降下はここではまだ主張しない。
-/

@[expose] public section

universe v u v' u'

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
