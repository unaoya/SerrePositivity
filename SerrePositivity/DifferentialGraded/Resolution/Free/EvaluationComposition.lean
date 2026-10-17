module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation

/-! # path評価と連結の整合性

## 概要
path評価と連結の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

omit D in
lemma evaluation_tensor_assoc {K L M : Complex A} {a b c d : E}
    (f : K ⟶ (a ⟶[Complex A] b)) (g : L ⟶ (b ⟶[Complex A] c))
    (h : M ⟶ (c ⟶[Complex A] d)) :
    (α_ K L M).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ eComp (Complex A) b c d)) ≫
        eComp (Complex A) a b d =
      (((f ⊗ₘ g) ≫ eComp (Complex A) a b c) ⊗ₘ h) ≫ eComp (Complex A) a c d := by
  have h₁ : (f ⊗ₘ (g ⊗ₘ h)) ≫ (𝟙 (a ⟶[Complex A] b) ⊗ₘ eComp (Complex A) b c d) =
      f ⊗ₘ ((g ⊗ₘ h) ≫ eComp (Complex A) b c d) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [← h₁]
  simp only [Category.assoc]
  rw [← reassoc_of% (associator_naturality f g h), id_tensorHom, e_assoc']
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

lemma wordEvaluation_concatenation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y))
    (p q : List D) (x y z : D) :
    (wordConcatenationIso A D K p q x y z).hom ≫
        wordEvaluation A D E K o f (concatenate D p q y) x z =
      (wordEvaluation A D E K o f p x y ⊗ₘ wordEvaluation A D E K o f q y z) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  induction p generalizing x with
  | nil => exact Category.id_comp _
  | cons b p ih =>
    change ((α_ (K x b) (wordTensor A D K p b y) (wordTensor A D K q y z)).hom ≫
        K x b ◁ (wordConcatenationIso A D K p q b y z).hom) ≫
        ((f x b ⊗ₘ wordEvaluation A D E K o f (concatenate D p q y) b z) ≫
          eComp (Complex A) (o x) (o b) (o z)) =
      (((f x b ⊗ₘ wordEvaluation A D E K o f p b y) ≫
        eComp (Complex A) (o x) (o b) (o y)) ⊗ₘ wordEvaluation A D E K o f q y z) ≫
          eComp (Complex A) (o x) (o y) (o z)
    have ht : (K x b ◁ (wordConcatenationIso A D K p q b y z).hom) ≫
        (f x b ⊗ₘ wordEvaluation A D E K o f (concatenate D p q y) b z) =
      f x b ⊗ₘ ((wordConcatenationIso A D K p q b y z).hom ≫
        wordEvaluation A D E K o f (concatenate D p q y) b z) := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
    rw [Category.assoc, ← Category.assoc _ _ (eComp (Complex A) (o x) (o b) (o z)), ht, ih]
    exact evaluation_tensor_assoc A E _ _ _

variable [Small.{u} D]

lemma pathEvaluation_composition (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) {x y z : D}
    (p : PathIndex D x y) (q : PathIndex D y z) :
    pathComposition A D K p q ≫ homEvaluation A D E K o f x z =
      (pathEvaluation A D E K o f p ⊗ₘ pathEvaluation A D E K o f q) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change ((λ_ (pathTensor A D K q)).hom ≫ pathInclusion A D K x z q) ≫ _ = _
    rw [Category.assoc, pathInclusion_homEvaluation]
    have hu : (eId (Complex A) (o x) ▷ (o x ⟶[Complex A] o z)) ≫
        eComp (Complex A) (o x) (o x) (o z) = (λ_ (o x ⟶[Complex A] o z)).hom := by
      have h := congrArg (fun k => (λ_ (o x ⟶[Complex A] o z)).hom ≫ k)
        (e_id_comp (Complex A) (o x) (o z))
      simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using h
    change _ = (eId (Complex A) (o x) ⊗ₘ pathEvaluation A D E K o f q) ≫ _
    rw [tensorHom_def, Category.assoc, ← whisker_exchange_assoc, hu]
    exact (leftUnitor_naturality _).symm
  | inr p =>
    cases q with
    | inl h =>
      rcases h with ⟨h⟩
      subst z
      change ((ρ_ (wordTensor A D K p x y)).hom ≫ pathInclusion A D K x y (.inr p)) ≫ _ = _
      rw [Category.assoc, pathInclusion_homEvaluation]
      change _ = (wordEvaluation A D E K o f p x y ⊗ₘ eId (Complex A) (o y)) ≫ _
      have hu : ((o x ⟶[Complex A] o y) ◁ eId (Complex A) (o y)) ≫
          eComp (Complex A) (o x) (o y) (o y) = (ρ_ (o x ⟶[Complex A] o y)).hom := by
        have h := congrArg (fun k => (ρ_ (o x ⟶[Complex A] o y)).hom ≫ k)
          (e_comp_id (Complex A) (o x) (o y))
        simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using h
      rw [tensorHom_def, Category.assoc, hu]
      exact (rightUnitor_naturality _).symm
    | inr q =>
      change ((wordConcatenationIso A D K p q x y z).hom ≫
          pathInclusion A D K x z (.inr (concatenate D p q y))) ≫ _ = _
      rw [Category.assoc, pathInclusion_homEvaluation]
      exact wordEvaluation_concatenation A D E K o f p q x y z

lemma homEvaluation_composition (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y z : D) :
    composition A D K x y z ≫ homEvaluation A D E K o f x z =
      (homEvaluation A D E K o f x y ⊗ₘ homEvaluation A D E K o f y z) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  apply tensorCoproduct_hom_ext (pathTensor A D K (x := x) (y := y))
    (pathTensor A D K (x := y) (y := z))
  intro p q
  change (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫
      (composition A D K x y z ≫ homEvaluation A D E K o f x z) =
    (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫
      ((homEvaluation A D E K o f x y ⊗ₘ homEvaluation A D E K o f y z) ≫
        eComp (Complex A) (o x) (o y) (o z))
  rw [← Category.assoc, composition_pathInclusion, pathEvaluation_composition,
    ← Category.assoc, tensorHom_comp_tensorHom, pathInclusion_homEvaluation,
    pathInclusion_homEvaluation]

end SerrePositivity.DifferentialGraded.FreeDGCategory
