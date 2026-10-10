module

public import SerrePositivity.CategoryTheory.TrianglePadding
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-! # 八面体の自明な直和因子の除去

Balmer–Schlichting の八面体のブロック形から、必要な三角形への retract を直接作る。
中間対象の包含と射影だけを補正するので、行列全体の共役変換は不要である。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

variable {U V W A B D : C}

/-- 八面体の第一の射のブロック形。 -/
def octahedronBlockFirst (f₁ : U ⟶ W) (f₂ : A ⟶ W) (f₃ : U ⟶ D) (f₄ : A ⟶ D) :
    (U ⊞ B) ⊞ A ⟶ (W ⊞ D) ⊞ A :=
  biprod.desc (biprod.desc (biprod.lift (biprod.lift f₁ f₃) 0) 0)
    (biprod.lift (biprod.lift f₂ f₄) (𝟙 A))

/-- 八面体の第二の射のブロック形。 -/
def octahedronBlockSecond (g₁ : W ⟶ V) (g₂ : A ⟶ V) (g₃ : W ⟶ D) (g₄ : A ⟶ D) :
    (W ⊞ D) ⊞ A ⟶ (V ⊞ D) ⊞ B⟦(1 : ℤ)⟧ :=
  biprod.desc (biprod.desc (biprod.lift (biprod.lift g₁ g₃) 0)
      (biprod.lift (biprod.lift 0 (𝟙 D)) 0))
    (biprod.lift (biprod.lift g₂ g₄) 0)

/-- 八面体の第三の射のブロック形。 -/
def octahedronBlockThird (h : V ⟶ U⟦(1 : ℤ)⟧) :
    (V ⊞ D) ⊞ B⟦(1 : ℤ)⟧ ⟶ ((U ⊞ B) ⊞ A)⟦(1 : ℤ)⟧ :=
  biprod.desc (biprod.desc (h ≫ (shiftFunctor C (1 : ℤ)).map
      ((biprod.inl : U ⟶ U ⊞ B) ≫ biprod.inl)) 0)
    ((shiftFunctor C (1 : ℤ)).map ((biprod.inr : B ⟶ U ⊞ B) ≫ biprod.inl))

/-- 第一の射は自明な因子上での二つの条件からブロック形に書ける。 -/
lemma octahedronBlockFirst_eq (F : (U ⊞ B) ⊞ A ⟶ (W ⊞ D) ⊞ A)
    (hB : ((biprod.inr : B ⟶ U ⊞ B) ≫ biprod.inl) ≫ F = 0)
    (hA : F ≫ biprod.snd = biprod.snd) :
    F = octahedronBlockFirst
      (biprod.inl ≫ biprod.inl ≫ F ≫ biprod.fst ≫ biprod.fst)
      (biprod.inr ≫ F ≫ biprod.fst ≫ biprod.fst)
      (biprod.inl ≫ biprod.inl ≫ F ≫ biprod.fst ≫ biprod.snd)
      (biprod.inr ≫ F ≫ biprod.fst ≫ biprod.snd) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · apply biprod.hom_ext <;> simp [octahedronBlockFirst, Category.assoc]
      · simp [octahedronBlockFirst, Category.assoc, hA]
    · simpa [octahedronBlockFirst, Category.assoc] using hB
  · apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp [octahedronBlockFirst, Category.assoc]
    · simp [octahedronBlockFirst, Category.assoc, hA]

/-- 第二の射の対応するブロック表示。 -/
lemma octahedronBlockSecond_eq (G : (W ⊞ D) ⊞ A ⟶ (V ⊞ D) ⊞ B⟦(1 : ℤ)⟧)
    (hD : ((biprod.inr : D ⟶ W ⊞ D) ≫ biprod.inl) ≫ G =
      (biprod.inr : D ⟶ V ⊞ D) ≫ biprod.inl)
    (hB : G ≫ biprod.snd = 0) :
    G = octahedronBlockSecond
      (biprod.inl ≫ biprod.inl ≫ G ≫ biprod.fst ≫ biprod.fst)
      (biprod.inr ≫ G ≫ biprod.fst ≫ biprod.fst)
      (biprod.inl ≫ biprod.inl ≫ G ≫ biprod.fst ≫ biprod.snd)
      (biprod.inr ≫ G ≫ biprod.fst ≫ biprod.snd) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · apply biprod.hom_ext <;> simp [octahedronBlockSecond, Category.assoc]
      · simp [octahedronBlockSecond, Category.assoc, hB]
    · simpa [octahedronBlockSecond, Category.assoc, biprod.lift_eq] using hD
  · apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp [octahedronBlockSecond, Category.assoc]
    · simp [octahedronBlockSecond, Category.assoc, hB]

/-- 合成が零であるブロック三角形から主対角成分の三角形への retract。 -/
def octahedronBlockRetract
    (f₁ : U ⟶ W) (f₂ : A ⟶ W) (f₃ : U ⟶ D) (f₄ : A ⟶ D)
    (g₁ : W ⟶ V) (g₂ : A ⟶ V) (g₃ : W ⟶ D) (g₄ : A ⟶ D)
    (h : V ⟶ U⟦(1 : ℤ)⟧)
    (hfg : octahedronBlockFirst (B := B) f₁ f₂ f₃ f₄ ≫
      octahedronBlockSecond (B := B) g₁ g₂ g₃ g₄ = 0) :
    Retract (Triangle.mk f₁ g₁ h)
      (Triangle.mk (octahedronBlockFirst (B := B) f₁ f₂ f₃ f₄)
        (octahedronBlockSecond (B := B) g₁ g₂ g₃ g₄)
        (octahedronBlockThird (A := A) (B := B) (D := D) h)) := by
  have hf : f₁ ≫ g₃ + f₃ = 0 := by
    have he := ((biprod.inl : U ⟶ U ⊞ B) ≫ biprod.inl) ≫= hfg =≫
      (biprod.fst ≫ (biprod.snd : V ⊞ D ⟶ D))
    simpa [octahedronBlockFirst, octahedronBlockSecond, biprod.lift_eq,
      Category.assoc, add_comp] using he
  have hg : f₂ ≫ g₁ + g₂ = 0 := by
    have he := (biprod.inr : A ⟶ (U ⊞ B) ⊞ A) ≫= hfg =≫
      (biprod.fst ≫ (biprod.fst : V ⊞ D ⟶ V))
    simpa [octahedronBlockFirst, octahedronBlockSecond, biprod.lift_eq,
      Category.assoc, add_comp] using he
  let i : Triangle.mk f₁ g₁ h ⟶
      Triangle.mk (octahedronBlockFirst (B := B) f₁ f₂ f₃ f₄)
        (octahedronBlockSecond (B := B) g₁ g₂ g₃ g₄)
        (octahedronBlockThird (A := A) (B := B) (D := D) h) :=
    { hom₁ := biprod.inl ≫ biprod.inl
      hom₂ := biprod.lift (biprod.lift (𝟙 W) (-g₃)) 0
      hom₃ := biprod.inl ≫ biprod.inl
      comm₁ := by
        dsimp
        apply biprod.hom_ext
        · apply biprod.hom_ext
          · simp [octahedronBlockFirst]
          · simpa [octahedronBlockFirst] using (eq_neg_of_add_eq_zero_right hf).symm
        · simp [octahedronBlockFirst]
      comm₂ := by
        dsimp
        apply biprod.hom_ext
        · apply biprod.hom_ext
          all_goals simp [octahedronBlockSecond, biprod.lift_eq, Category.assoc, add_comp]
        · simp [octahedronBlockSecond, biprod.lift_eq, Category.assoc, add_comp]
      comm₃ := by simp [octahedronBlockThird] }
  let r : Triangle.mk (octahedronBlockFirst (B := B) f₁ f₂ f₃ f₄)
      (octahedronBlockSecond (B := B) g₁ g₂ g₃ g₄)
      (octahedronBlockThird (A := A) (B := B) (D := D) h) ⟶ Triangle.mk f₁ g₁ h :=
    { hom₁ := biprod.fst ≫ biprod.fst
      hom₂ := biprod.desc biprod.fst (-f₂)
      hom₃ := biprod.fst ≫ biprod.fst
      comm₁ := by
        dsimp
        apply biprod.hom_ext'
        · apply biprod.hom_ext'
          all_goals simp [octahedronBlockFirst, biprod.lift_eq, Category.assoc, add_comp]
        · simp [octahedronBlockFirst, biprod.lift_eq, Category.assoc, add_comp]
      comm₂ := by
        dsimp
        apply biprod.hom_ext'
        · apply biprod.hom_ext'
          all_goals simp [octahedronBlockSecond]
        · simpa [octahedronBlockSecond] using (eq_neg_of_add_eq_zero_right hg)
      comm₃ := by
        dsimp
        apply biprod.hom_ext'
        · apply biprod.hom_ext'
          all_goals simp [octahedronBlockThird, ← CategoryTheory.Functor.map_comp,
            Category.assoc]
        · simp [octahedronBlockThird, ← CategoryTheory.Functor.map_comp, Category.assoc] }
  exact ⟨i, r, by
    apply TriangleMorphism.ext
    · simp [i, r]
    · simp [i, r, biprod.lift_eq, add_comp, Category.assoc]
    · simp [i, r]⟩

end

end SerrePositivity
