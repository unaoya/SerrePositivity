module

public import SerrePositivity.Spectra.SymmetricSequence.Evaluation
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # 自由対称列の次数と置換作用

自由対称列は生成する次数以外で始対象となる。
その次数では全ての置換に対応する生成元を持ち、全単射の作用は添字の後合成である。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
  [∀ a b : FiniteBijection, HasCoproductsOfShape (a ⟶ b) C]

/-- 自由対称列への余積の各包含。 -/
def freeAtInclusion (n : ℕ) (X : C) {a : FiniteBijection} (h : FiniteBijection.of n ⟶ a) :
    X ⟶ ((freeAt n).obj X).obj a := Sigma.ι (fun _ : FiniteBijection.of n ⟶ a => X) h

/-- 全単射の作用は余積の添字を後合成する。 -/
@[reassoc] lemma freeAtInclusion_map (n : ℕ) (X : C) {a b : FiniteBijection}
    (h : FiniteBijection.of n ⟶ a) (k : a ⟶ b) :
    freeAtInclusion n X h ≫ ((freeAt n).obj X).map k = freeAtInclusion n X (h ≫ k) := by
  change Sigma.ι (fun _ : FiniteBijection.of n ⟶ a => X) h ≫
    Sigma.desc (fun g => Sigma.ι (fun _ : FiniteBijection.of n ⟶ b => X) (g ≫ k)) =
      Sigma.ι (fun _ : FiniteBijection.of n ⟶ b => X) (h ≫ k)
  simp

/-- 入力の射は全ての余積成分に同じ射を作用させる。 -/
@[reassoc] lemma freeAtInclusion_map_input (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {a : FiniteBijection} (h : FiniteBijection.of n ⟶ a) :
    freeAtInclusion n X h ≫ ((freeAt n).map f).app a = f ≫ freeAtInclusion n Y h := by
  change Sigma.ι (fun _ : FiniteBijection.of n ⟶ a => X) h ≫
    Sigma.desc (fun g => f ≫ Sigma.ι (fun _ : FiniteBijection.of n ⟶ a => Y) g) =
      f ≫ Sigma.ι (fun _ : FiniteBijection.of n ⟶ a => Y) h
  simp

/-- 自由対称列の各段からの射は全ての余積成分上の値で決まる。 -/
lemma freeAt_obj_hom_ext (n : ℕ) (X : C) (a : FiniteBijection) {Y : C}
    (f g : ((freeAt n).obj X).obj a ⟶ Y)
    (h : ∀ k : FiniteBijection.of n ⟶ a,
      freeAtInclusion n X k ≫ f = freeAtInclusion n X k ≫ g) : f = g := by
  apply Sigma.hom_ext
  exact h

/-- 全ての余積成分は、恒等全単射の生成元から移送して得られる。 -/
@[reassoc] lemma freeAtInclusion_eq_generator (n : ℕ) (X : C)
    {a : FiniteBijection} (h : FiniteBijection.of n ⟶ a) :
    freeAtGenerator n X ≫ ((freeAt n).obj X).map h = freeAtInclusion n X h := by
  have hi := freeAtInclusion_map n X (𝟙 (FiniteBijection.of n)) h
  erw [Category.id_comp] at hi
  exact hi

/-- 生成する次数以外の段は、空の添字の余積として始対象になる。 -/
def freeAtLevelInitial (n m : ℕ) (X : C) (h : n ≠ m) :
    IsInitial (level ((freeAt n).obj X) m) := by
  letI : IsEmpty (FiniteBijection.of n ⟶ FiniteBijection.of m) :=
    ⟨fun k => h (FiniteBijection.card_eq_of_hom k)⟩
  apply IsInitial.ofUniqueHom (fun Y => Sigma.desc (fun k => isEmptyElim k))
  intro Y f
  apply Sigma.hom_ext
  intro k
  exact isEmptyElim k

/-- 任意の有限集合の濃度がnと異なる場合の始対象性。 -/
def freeAtObjInitial (n : ℕ) (X : C) (a : FiniteBijection)
    (h : n ≠ FiniteBijection.card a) : IsInitial (((freeAt n).obj X).obj a) := by
  have ha := freeAtLevelInitial n (FiniteBijection.card a) X h
  simpa only [level, FiniteBijection.of_card] using ha

/-- 第n段の、置換に対応する生成元。 -/
def freeAtPermutationInclusion (n : ℕ) (X : C) (σ : Equiv.Perm (Fin n)) :
    X ⟶ level ((freeAt n).obj X) n := freeAtInclusion n X (FiniteBijection.permutation n σ)

/-- 第n段の置換作用は、生成元の置換に左から乗じる。 -/
@[reassoc] lemma freeAtPermutationInclusion_action (n : ℕ) (X : C)
    (σ τ : Equiv.Perm (Fin n)) :
    freeAtPermutationInclusion n X σ ≫
      ((freeAt n).obj X).map (FiniteBijection.permutation n τ) =
        freeAtPermutationInclusion n X (τ * σ) := by
  erw [freeAtPermutationInclusion, freeAtInclusion_map,
    ← FiniteBijection.permutation_mul]
  rfl

end SerrePositivity.SymmetricSequence
