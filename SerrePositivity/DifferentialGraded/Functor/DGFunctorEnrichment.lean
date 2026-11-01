module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorParamComposition
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomIdentity

/-! # 全次数 Hom end による厳密 dg 関手圏の豊穣構造
概要：厳密 dg 関手を対象とし、全次数自然変換の Hom end を持つ dg 圏を構成する。
方針：元の各対象の合成を end へ持ち上げ、全対象評価で圏法則を検査する。
規約：Mathlib の通常自然変換圏で代用しない。使われ方：dg 入力の高次 Hom。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]

/-- 元の全対象の合成を保持する、dg 関手 Hom end の合成。 -/
def dgFunctorComposition (M N P : DGFunctor A D E) :
    dgFunctorHom A D E M N ⊗ dgFunctorHom A D E N P ⟶ dgFunctorHom A D E M P :=
  (dgFunctorHomEquiv A D E _ M P).symm (dgFunctorParamCompose A D E
    ((dgFunctorHomEquiv A D E _ M N) (𝟙 _)) ((dgFunctorHomEquiv A D E _ N P) (𝟙 _)))

/-- Hom end の合成の全対象評価は、同じ元の豊穣合成。 -/
@[reassoc (attr := simp)]
lemma dgFunctorComposition_π (M N P : DGFunctor A D E) (x : D) :
    dgFunctorComposition A D E M N P ≫ dgFunctorHomπ A D E M P x =
      (dgFunctorHomπ A D E M N x ⊗ₘ dgFunctorHomπ A D E N P x) ≫
        eComp (Complex A) _ _ _ := by
  rw [dgFunctorComposition, dgFunctorHomEquiv_symm_π]
  change ((𝟙 _ ≫ dgFunctorHomπ A D E M N x) ⊗ₘ
    (𝟙 _ ≫ dgFunctorHomπ A D E N P x)) ≫ eComp (Complex A) _ _ _ = _
  rw [Category.id_comp, Category.id_comp]

/-- Hom end の合成と元の閉単位は左単位律を満たす。 -/
lemma dgFunctorIdentity_comp (M N : DGFunctor A D E) :
    (λ_ (dgFunctorHom A D E M N)).inv ≫ dgFunctorIdentity A D E M ▷ _ ≫
      dgFunctorComposition A D E M M N = 𝟙 _ := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, Category.assoc, dgFunctorComposition_π]
  change _ ≫ (dgFunctorIdentity A D E M ⊗ₘ 𝟙 _) ≫
    (dgFunctorHomπ A D E M M x ⊗ₘ dgFunctorHomπ A D E M N x) ≫
      eComp (Complex A) _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [dgFunctorIdentity_π, Category.id_comp]
  rw [tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc,
    e_id_comp, Category.comp_id]

/-- Hom end の合成と元の閉単位は右単位律を満たす。 -/
lemma dgFunctorComp_identity (M N : DGFunctor A D E) :
    (ρ_ (dgFunctorHom A D E M N)).inv ≫ _ ◁ dgFunctorIdentity A D E N ≫
      dgFunctorComposition A D E M N N = 𝟙 _ := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, Category.assoc, dgFunctorComposition_π]
  change _ ≫ (𝟙 _ ⊗ₘ dgFunctorIdentity A D E N) ≫
    (dgFunctorHomπ A D E M N x ⊗ₘ dgFunctorHomπ A D E N N x) ≫
      eComp (Complex A) _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [dgFunctorIdentity_π, Category.id_comp]
  rw [tensorHom_def, Category.assoc, ← rightUnitor_inv_naturality_assoc,
    e_comp_id, Category.comp_id]

/-- Hom end の縦合成は、元の全対象の結合律を保つ。 -/
lemma dgFunctorComposition_assoc (M N P Q : DGFunctor A D E) :
    (α_ (dgFunctorHom A D E M N) (dgFunctorHom A D E N P)
      (dgFunctorHom A D E P Q)).inv ≫
      dgFunctorComposition A D E M N P ▷ _ ≫ dgFunctorComposition A D E M P Q =
    _ ◁ dgFunctorComposition A D E N P Q ≫ dgFunctorComposition A D E M N Q := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFunctorComposition_π]
  change (α_ _ _ _).inv ≫ (dgFunctorComposition A D E M N P ⊗ₘ 𝟙 _) ≫
      (dgFunctorHomπ A D E M P x ⊗ₘ dgFunctorHomπ A D E P Q x) ≫
        eComp (Complex A) _ _ _ =
    (𝟙 _ ⊗ₘ dgFunctorComposition A D E N P Q) ≫
      (dgFunctorHomπ A D E M N x ⊗ₘ dgFunctorHomπ A D E N Q x) ≫ eComp (Complex A) _ _ _
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, dgFunctorComposition_π]
  rw [← tensorHom_comp_whiskerRight_assoc
    (dgFunctorHomπ A D E M N x ⊗ₘ dgFunctorHomπ A D E N P x)
    (eComp (Complex A) _ _ _) (dgFunctorHomπ A D E P Q x)]
  rw [← tensorHom_comp_whiskerLeft_assoc (dgFunctorHomπ A D E M N x)
    (dgFunctorHomπ A D E N P x ⊗ₘ dgFunctorHomπ A D E P Q x) (eComp (Complex A) _ _ _)]
  rw [← associator_inv_naturality_assoc (dgFunctorHomπ A D E M N x)
    (dgFunctorHomπ A D E N P x) (dgFunctorHomπ A D E P Q x), e_assoc]

/-- 全次数の実自然変換 end を持つ、厳密 dg 関手の dg 圏。 -/
instance dgFunctorEnrichment : DGCategory A (DGFunctor A D E) :=
  ofHomObjects A (DGFunctor A D E) (dgFunctorHom A D E) (dgFunctorIdentity A D E)
    (dgFunctorComposition A D E) (dgFunctorIdentity_comp A D E) (dgFunctorComp_identity A D E)
    (dgFunctorComposition_assoc A D E)

/-- 厳密 dg 関手の全対象評価は、同じ元の評価を持つ dg 関手。 -/
def dgFunctorEvaluationDG (x : D) : DGFunctor A (DGFunctor A D E) E where
  obj F := F.obj x
  map M N := dgFunctorHomπ A D E M N x
  map_id M := dgFunctorIdentity_π A D E M x
  map_comp M N P := dgFunctorComposition_π A D E M N P x

end SerrePositivity.KST.SConstruction
