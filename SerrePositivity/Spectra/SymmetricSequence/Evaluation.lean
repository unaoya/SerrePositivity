module

public import SerrePositivity.Spectra.SymmetricSequence.Basic
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # 対称列の各段の評価と自由生成

Mathlibの評価の左随伴を対称列の型へ移す。第n段を生成する対称列の第m段は、
nからmへの全単射で添字付けたXの余積である。入力には置換作用を要求しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- 置換作用を忘れた第n段の評価。 -/
def evaluation (n : ℕ) : SymmetricSequence C ⥤ C :=
  toFunctorCategory ⋙ (CategoryTheory.evaluation FiniteBijection C).obj (FiniteBijection.of n)

variable [∀ a b : FiniteBijection, HasCoproductsOfShape (a ⟶ b) C]

/-- 第n段にXを自由生成する対称列の関手。 -/
def freeAt (n : ℕ) : C ⥤ SymmetricSequence C :=
  evaluationLeftAdjoint C (FiniteBijection.of n) ⋙ fromFunctorCategory

/-- 自由生成する対称列と第n段の評価との随伴。 -/
def freeAtAdjunction (n : ℕ) : freeAt (C := C) n ⊣ evaluation n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X F => (evaluationAdjunctionRight C (FiniteBijection.of n)).homEquiv X F
      homEquiv_naturality_left_symm := fun f g =>
        (evaluationAdjunctionRight C (FiniteBijection.of n)).homEquiv_naturality_left_symm f g
      homEquiv_naturality_right := fun f g =>
        (evaluationAdjunctionRight C (FiniteBijection.of n)).homEquiv_naturality_right f g }

/-- 自由対称列の各段は全単射で添字付けた余積。 -/
lemma freeAt_level (n m : ℕ) (X : C) :
    level ((freeAt n).obj X) m =
      ∐ (fun _ : FiniteBijection.of n ⟶ FiniteBijection.of m => X) := rfl

/-- 生成元は恒等全単射に対応する余積への包含。 -/
def freeAtGenerator (n : ℕ) (X : C) : X ⟶ level ((freeAt n).obj X) n :=
  Sigma.ι (fun _ : FiniteBijection.of n ⟶ FiniteBijection.of n => X) (𝟙 _)

/-- 第n段で指定された射を、自由対称列全体の射へ延長する。 -/
def freeAtLift (n : ℕ) {X : C} (F : SymmetricSequence C) (f : X ⟶ level F n) :
    (freeAt n).obj X ⟶ F :=
  (freeAtAdjunction n).homEquiv X F |>.symm f

/-- 延長の成分は全単射による移送を余積の普遍性でまとめた射。 -/
lemma freeAtLift_app (n m : ℕ) {X : C} (F : SymmetricSequence C)
    (f : X ⟶ level F n) :
    (freeAtLift n F f).app (FiniteBijection.of m) =
      Sigma.desc (fun h : FiniteBijection.of n ⟶ FiniteBijection.of m => f ≫ F.map h) := by
  simp [freeAtLift, freeAtAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    evaluationAdjunctionRight]
  rfl

/-- 生成元への制限は随伴のHom同値である。 -/
lemma freeAtHomEquiv_apply (n : ℕ) (X : C) (F : SymmetricSequence C)
    (f : (freeAt n).obj X ⟶ F) :
    (freeAtAdjunction n).homEquiv X F f =
      freeAtGenerator n X ≫ f.app (FiniteBijection.of n) := by
  simp [freeAtAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    evaluationAdjunctionRight, freeAtGenerator]
  rfl

/-- 随伴の単位は恒等全単射に対応する生成元の包含。 -/
lemma freeAt_unit (n : ℕ) (X : C) :
    (freeAtAdjunction n).unit.app X = freeAtGenerator n X := by
  have h := freeAtHomEquiv_apply n X ((freeAt n).obj X) (𝟙 _)
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at h
  change (freeAtAdjunction n).unit.app X ≫ 𝟙 _ = freeAtGenerator n X ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- 延長は生成元上で指定された射に一致する。 -/
lemma freeAtGenerator_lift (n : ℕ) {X : C} (F : SymmetricSequence C)
    (f : X ⟶ level F n) :
    freeAtGenerator n X ≫ (freeAtLift n F f).app (FiniteBijection.of n) = f := by
  rw [← freeAtHomEquiv_apply]
  exact (freeAtAdjunction n).homEquiv X F |>.apply_symm_apply f

/-- 自由対称列からの射は生成元上の値で一意に決まる。 -/
lemma freeAtLift_unique (n : ℕ) {X : C} (F : SymmetricSequence C)
    (f : (freeAt n).obj X ⟶ F) (g : X ⟶ level F n)
    (h : freeAtGenerator n X ≫ f.app (FiniteBijection.of n) = g) :
    f = freeAtLift n F g := by
  apply ((freeAtAdjunction n).homEquiv X F).injective
  rw [freeAtHomEquiv_apply, h]
  exact (((freeAtAdjunction n).homEquiv X F).apply_symm_apply g).symm

end SerrePositivity.SymmetricSequence
