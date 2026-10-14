module
public import SerrePositivity.DifferentialGraded.Complexes.Composition
public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Ch(A) 豊穣としての dg 圏

別の dg 圏構造体は導入しない。Z⁰ は Mathlib の ForgetEnrichment をそのまま使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory MonoidalPreadditive
variable (A : Type u) [CommRing A]

/-- 主モデルは非有界 Ch(A) による Mathlib の豊穣圏。対象宇宙 v は独立。 -/
abbrev DGCategory (D : Type v) := EnrichedCategory (Complex A) D

variable (D : Type v) [DGCategory A D]

/-- 閉次数零の圏。単位複体から Hom 複体への chain map を射にする。 -/
abbrev ClosedCategory := ForgetEnrichment (Complex A) D

/-- 既存の豊穣構造から Hom 複体を取り出す。 -/
abbrev homObject (x y : D) : Complex A := x ⟶[Complex A] y

/-- 豊穣合成の源は Hom(x,y)⊗Hom(y,z)。通常順とは Koszul 交換が必要。 -/
abbrev forwardComposition (x y z : D) := eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z)

/-- 豊穣構造の constructor。入力は Hom 複体・閉単位・chain map 合成と三つの圏法則。
既存 EnrichedCategory の constructor に直接渡し、独立した公開構造を持たない。 -/
@[instance_reducible]
def ofHomObjects (H : D → D → Complex A)
    (unit : ∀ x, 𝟙_ (Complex A) ⟶ H x x)
    (comp : ∀ x y z, H x y ⊗ H y z ⟶ H x z)
    (left : ∀ x y, (λ_ (H x y)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _)
    (right : ∀ x y, (ρ_ (H x y)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _)
    (assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
      _ ◁ comp x y z ≫ comp w x z) : DGCategory A D where
  Hom := H
  id := unit
  comp := comp
  id_comp := left
  comp_id := right
  assoc := assoc

omit [DGCategory A D] in
/-- constructor と accessor の Hom 成分は定義上往復する。 -/
lemma ofHomObjects_hom (H : D → D → Complex A) (unit comp left right assoc) (x y : D) :
    (ofHomObjects A D H unit comp left right assoc).Hom x y = H x y := rfl

/-- Enriched の accessor から元の豊穣構造を復元する。 -/
lemma ofHomObjects_recover :
    ofHomObjects A D (EnrichedCategory.Hom (V := Complex A))
      (eId (Complex A)) (eComp (Complex A)) (e_id_comp (Complex A))
      (e_comp_id (Complex A)) (e_assoc (Complex A)) =
        (inferInstance : DGCategory A D) := rfl

omit [DGCategory A D] in
/-- 双次数合成を入力する constructor。微分との両立から chain map を構成する。
単位・結合則はその chain map に対する法則として要求する。 -/
@[instance_reducible]
def ofComponents (H : D → D → Complex A)
    (unit : ∀ x, 𝟙_ (Complex A) ⟶ H x x)
    (b : ∀ x y z (i j n : ℤ), i + j = n → ((H x y).X i ⊗ (H y z).X j ⟶ (H x z).X n))
    (db : ∀ x y z i j,
      b x y z i j (i + j) rfl ≫ (H x z).d (i + j) (i + j + 1) =
        ((H x y).d i (i + 1) ▷ (H y z).X j) ≫
          b x y z (i + 1) j (i + j + 1) (by omega) +
        i.negOnePow • (((H x y).X i ◁ (H y z).d j (j + 1)) ≫
          b x y z i (j + 1) (i + j + 1) (by omega)))
    (left : ∀ x y, (λ_ (H x y)).inv ≫ unit x ▷ _ ≫
      tensorLift (b x x y) (db x x y) = 𝟙 _)
    (right : ∀ x y, (ρ_ (H x y)).inv ≫ _ ◁ unit y ≫
      tensorLift (b x y y) (db x y y) = 𝟙 _)
    (assoc : ∀ w x y z, (α_ _ _ _).inv ≫
      tensorLift (b w x y) (db w x y) ▷ _ ≫ tensorLift (b w y z) (db w y z) =
      _ ◁ tensorLift (b x y z) (db x y z) ≫ tensorLift (b w x z) (db w x z)) :
    DGCategory A D :=
  ofHomObjects A D H unit (fun x y z => tensorLift (b x y z) (db x y z)) left right assoc

/-- Z⁰ の各 Hom に単位からの chain map の加法群を使う。 -/
instance closedHomGroup (x y : ClosedCategory A D) : AddCommGroup (x ⟶ y) :=
  inferInstanceAs (AddCommGroup (𝟙_ (Complex A) ⟶ homObject A D x y))

/-- Z⁰ の合成は加法的。 -/
instance closedPreadditive : Preadditive (ClosedCategory A D) where
  homGroup := closedHomGroup A D
  add_comp := by
    intro x y z f g h
    change (λ_ (𝟙_ (Complex A))).inv ≫
      ((ForgetEnrichment.homTo (Complex A) f + ForgetEnrichment.homTo (Complex A) g) ⊗ₘ
        ForgetEnrichment.homTo (Complex A) h) ≫ _ = _
    simp only [add_tensor, Preadditive.comp_add, Preadditive.add_comp]
    rfl
  comp_add := by
    intro x y z f g h
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) f ⊗ₘ
        (ForgetEnrichment.homTo (Complex A) g + ForgetEnrichment.homTo (Complex A) h)) ≫ _ = _
    simp only [tensor_add, Preadditive.comp_add, Preadditive.add_comp]
    rfl

/-- Z⁰ の各 Hom に chain map の A 加群構造を使う。 -/
instance closedHomModule (x y : ClosedCategory A D) : Module A (x ⟶ y) :=
  inferInstanceAs (Module A (𝟙_ (Complex A) ⟶ homObject A D x y))

/-- Z⁰ の A 線形構造。 -/
instance closedLinear : Linear A (ClosedCategory A D) where
  homModule := closedHomModule A D
  smul_comp := by
    intro x y z a f g
    change (λ_ (𝟙_ (Complex A))).inv ≫
      ((a • ForgetEnrichment.homTo (Complex A) f) ⊗ₘ ForgetEnrichment.homTo (Complex A) g) ≫
      eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z) =
      a • (((λ_ (𝟙_ (Complex A))).inv ≫
        (ForgetEnrichment.homTo (Complex A) f ⊗ₘ ForgetEnrichment.homTo (Complex A) g)) ≫
          eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
  comp_smul := by
    intro x y z f a g
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) f ⊗ₘ (a • ForgetEnrichment.homTo (Complex A) g)) ≫
      eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z) =
      a • (((λ_ (𝟙_ (Complex A))).inv ≫
        (ForgetEnrichment.homTo (Complex A) f ⊗ₘ ForgetEnrichment.homTo (Complex A) g)) ≫
          eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
            (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
    simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
end SerrePositivity.DifferentialGraded
