module
public import SerrePositivity.KST.SConstruction.PointedKanLoopInfinity
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 豊穣関手の有向 collage
概要：下段 D・上段 C と、下段 X から上段 Y への Hom_D(X, RY) を持つ豊穣圏。
方針：逆方向の Hom を空にし、交差合成に R の全写像空間の作用を使う。
規約：豊穣関手 R の単位・合成法則だけを使い、未構成の ∞ 随伴を仮定しない。
使われ方：全入力円柱の交差写像空間に随伴同型を適用するための値域。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 逆向きの写像空間に使う空な単体集合。 -/
def enrichedCollageEmpty : SSet.{u} :=
  (CategoryTheory.Functor.const (SimplexCategoryᵒᵖ)).obj PEmpty.{u + 1}

/-- 空な写像空間は全単体次数で空。 -/
instance enrichedCollageEmpty_isEmpty (n : SimplexCategoryᵒᵖ) :
    IsEmpty (enrichedCollageEmpty.{u}.obj n) := inferInstanceAs (IsEmpty PEmpty.{u + 1})

/-- 空な写像空間から任意の単体集合への唯一の射。 -/
def enrichedCollageEmptyMap (X : SSet.{u}) : enrichedCollageEmpty ⟶ X where
  app _ := ↾fun x => PEmpty.elim x
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact PEmpty.elim x

/-- 逆向きの空な写像空間も Kan。 -/
instance enrichedCollageEmpty_kanComplex : KanComplex enrichedCollageEmpty.{u} := by
  rw [KanComplex.iff]
  intro n i f _
  obtain ⟨j, hj⟩ := exists_ne i
  exact PEmpty.elim ((f j hj).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))

private lemma hom_ext_of_empty {A B : SSet.{u}} (h : ∀ n, IsEmpty (A.obj n))
    (f g : A ⟶ B) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  let : IsEmpty (A.obj n) := h n
  exact isEmptyElim x

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 関手 R を固定した、有向 collage の対象の型。 -/
@[nolint unusedArguments]
def EnrichedFunctorCollage (_R : EnrichedFunctor SSet.{u} C D) : Type v := D ⊕ C

/-- 同段の元の Hom、交差 Hom_D(X,RY)、逆向きの空な Hom。 -/
def enrichedFunctorCollageHom (R : EnrichedFunctor SSet.{u} C D)
    (X Y : EnrichedFunctorCollage R) : SSet.{u} :=
  match X, Y with
  | .inl X, .inl Y => SimplicialCategory.sHom X Y
  | .inl X, .inr Y => SimplicialCategory.sHom X (R.obj Y)
  | .inr _, .inl _ => enrichedCollageEmpty
  | .inr X, .inr Y => SimplicialCategory.sHom X Y

/-- 各段の元の豊穣単位。 -/
def enrichedFunctorCollageId (R : EnrichedFunctor SSet.{u} C D)
    (X : EnrichedFunctorCollage R) : 𝟙_ SSet ⟶ enrichedFunctorCollageHom R X X :=
  match X with
  | .inl X => eId SSet X
  | .inr X => eId SSet X

/-- 交差合成では R の全写像空間の作用を使い、逆向きの合成は空な始域から定める。 -/
def enrichedFunctorCollageComp (R : EnrichedFunctor SSet.{u} C D)
    (X Y Z : EnrichedFunctorCollage R) :
    enrichedFunctorCollageHom R X Y ⊗ enrichedFunctorCollageHom R Y Z ⟶
      enrichedFunctorCollageHom R X Z :=
  match X, Y, Z with
  | .inl X, .inl Y, .inl Z => eComp SSet X Y Z
  | .inl X, .inl Y, .inr Z => eComp SSet X Y (R.obj Z)
  | .inl X, .inr Y, .inr Z =>
      (𝟙 (SimplicialCategory.sHom X (R.obj Y)) ⊗ₘ R.map Y Z) ≫
        eComp SSet X (R.obj Y) (R.obj Z)
  | .inr X, .inr Y, .inr Z => eComp SSet X Y Z
  | .inl X, .inr _, .inl Z =>
      snd _ _ ≫ enrichedCollageEmptyMap (SimplicialCategory.sHom X Z)
  | .inr _, .inl _, .inl _ => fst _ _ ≫ enrichedCollageEmptyMap enrichedCollageEmpty
  | .inr X, .inl _, .inr Z =>
      fst _ _ ≫ enrichedCollageEmptyMap (SimplicialCategory.sHom X Z)
  | .inr _, .inr _, .inl _ => snd _ _ ≫ enrichedCollageEmptyMap enrichedCollageEmpty

/-- 有向 collage の豊穣左単位律。 -/
lemma enrichedFunctorCollage_id_comp (R : EnrichedFunctor SSet.{u} C D)
    (X Y : EnrichedFunctorCollage R) :
    (λ_ (enrichedFunctorCollageHom R X Y)).inv ≫
        enrichedFunctorCollageId R X ▷ _ ≫ enrichedFunctorCollageComp R X X Y = 𝟙 _ := by
  rcases X with X | X <;> rcases Y with Y | Y
  · exact e_id_comp SSet X Y
  · exact e_id_comp SSet X (R.obj Y)
  · exact hom_ext_of_empty (fun n => enrichedCollageEmpty_isEmpty n) _ _
  · exact e_id_comp SSet X Y

/-- 有向 collage の豊穣右単位律。 -/
lemma enrichedFunctorCollage_comp_id (R : EnrichedFunctor SSet.{u} C D)
    (X Y : EnrichedFunctorCollage R) :
    (ρ_ (enrichedFunctorCollageHom R X Y)).inv ≫
        _ ◁ enrichedFunctorCollageId R Y ≫ enrichedFunctorCollageComp R X Y Y = 𝟙 _ := by
  rcases X with X | X <;> rcases Y with Y | Y
  · exact e_comp_id SSet X Y
  · change (ρ_ (SimplicialCategory.sHom X (R.obj Y))).inv ≫
      _ ◁ eId SSet Y ≫
        (𝟙 (SimplicialCategory.sHom X (R.obj Y)) ⊗ₘ R.map Y Y) ≫
          eComp SSet X (R.obj Y) (R.obj Y) = 𝟙 _
    rw [id_tensorHom, ← whiskerLeft_comp_assoc, R.map_id]
    exact e_comp_id SSet X (R.obj Y)
  · exact hom_ext_of_empty (fun n => enrichedCollageEmpty_isEmpty n) _ _
  · exact e_comp_id SSet X Y

private lemma collage_assoc_0011 (R : EnrichedFunctor SSet.{u} C D)
    (W X : D) (Y Z : C) :
    (α_ (SimplicialCategory.sHom W X) (SimplicialCategory.sHom X (R.obj Y))
        (SimplicialCategory.sHom Y Z)).inv ≫
      eComp SSet W X (R.obj Y) ▷ _ ≫
        (𝟙 (SimplicialCategory.sHom W (R.obj Y)) ⊗ₘ R.map Y Z) ≫
          eComp SSet W (R.obj Y) (R.obj Z) =
    (SimplicialCategory.sHom W X) ◁
        ((𝟙 (SimplicialCategory.sHom X (R.obj Y)) ⊗ₘ R.map Y Z) ≫
          eComp SSet X (R.obj Y) (R.obj Z)) ≫ eComp SSet W X (R.obj Z) := by
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc, e_assoc]

private lemma collage_assoc_0111 (R : EnrichedFunctor SSet.{u} C D)
    (W : D) (X Y Z : C) :
    (α_ (SimplicialCategory.sHom W (R.obj X)) (SimplicialCategory.sHom X Y)
        (SimplicialCategory.sHom Y Z)).inv ≫
      ((𝟙 (SimplicialCategory.sHom W (R.obj X)) ⊗ₘ R.map X Y) ≫
        eComp SSet W (R.obj X) (R.obj Y)) ▷ _ ≫
          (𝟙 (SimplicialCategory.sHom W (R.obj Y)) ⊗ₘ R.map Y Z) ≫
            eComp SSet W (R.obj Y) (R.obj Z) =
    (SimplicialCategory.sHom W (R.obj X)) ◁ eComp SSet X Y Z ≫
        (𝟙 (SimplicialCategory.sHom W (R.obj X)) ⊗ₘ R.map X Z) ≫
          eComp SSet W (R.obj X) (R.obj Z) := by
  simp only [id_tensorHom, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, ← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_right_assoc, e_assoc]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← tensorHom_def, ← R.map_comp]
  simp only [whiskerLeft_comp, Category.assoc]

/-- 有向 collage の豊穣結合律。 -/
lemma enrichedFunctorCollage_assoc (R : EnrichedFunctor SSet.{u} C D)
    (W X Y Z : EnrichedFunctorCollage R) :
    (α_ (enrichedFunctorCollageHom R W X) (enrichedFunctorCollageHom R X Y)
        (enrichedFunctorCollageHom R Y Z)).inv ≫
      enrichedFunctorCollageComp R W X Y ▷ (enrichedFunctorCollageHom R Y Z) ≫
        enrichedFunctorCollageComp R W Y Z =
      (enrichedFunctorCollageHom R W X) ◁ enrichedFunctorCollageComp R X Y Z ≫
        enrichedFunctorCollageComp R W X Z := by
  rcases W with W | W <;> rcases X with X | X <;>
    rcases Y with Y | Y <;> rcases Z with Z | Z
  · exact e_assoc SSet W X Y Z
  · exact e_assoc SSet W X Y (R.obj Z)
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.2⟩
  · exact collage_assoc_0011 R W X Y Z
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.2⟩
  · exact collage_assoc_0111 R W X Y Z
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.1⟩
  · apply hom_ext_of_empty
    intro n
    exact ⟨fun x => PEmpty.elim x.2.2⟩
  · exact e_assoc SSet W X Y Z

/-- 下段・上段・交差 Hom と R の作用から構成した単体的豊穣圏。 -/
instance enrichedFunctorCollage_enrichedCategory (R : EnrichedFunctor SSet.{u} C D) :
    EnrichedCategory SSet.{u} (EnrichedFunctorCollage R) where
  Hom := enrichedFunctorCollageHom R
  id := enrichedFunctorCollageId R
  comp := enrichedFunctorCollageComp R
  id_comp := enrichedFunctorCollage_id_comp R
  comp_id := enrichedFunctorCollage_comp_id R
  assoc := enrichedFunctorCollage_assoc R

end SerrePositivity.KST.SConstruction
