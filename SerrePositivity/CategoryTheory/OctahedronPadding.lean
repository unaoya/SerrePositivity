module

public import SerrePositivity.CategoryTheory.OctahedronBlockRetract
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # 自明な因子を加えた八面体からの降下 -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive CategoryTheory.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

variable {X Y Z U V W : C} {u : X ⟶ Y} {v : Y ⟶ Z} {w : X ⟶ Z}
  (comm : u ≫ v = w)
  {a : Y ⟶ U} {b : U ⟶ X⟦(1 : ℤ)⟧} (h₁ : Triangle.mk u a b ∈ distTriang C)
  {c : Z ⟶ V} {d : V ⟶ Y⟦(1 : ℤ)⟧} (h₂ : Triangle.mk v c d ∈ distTriang C)
  {e : Z ⟶ W} {f : W ⟶ X⟦(1 : ℤ)⟧} (h₃ : Triangle.mk w e f ∈ distTriang C)
  (A B D : C)

include comm in
lemma paddedTriangle_comp :
    (paddedTriangle (Triangle.mk u a b) A B).mor₁ ≫
      (paddedTriangle (Triangle.mk v c d) B D).mor₁ =
        (paddedTriangle (Triangle.mk w e f) A D).mor₁ := by
  dsimp [paddedTriangle, triangleAddSource, triangleAddTarget]
  simp only [Category.assoc, biprod.inl_fst_assoc]
  rw [← Category.assoc u v, comm]

variable (H : Octahedron (paddedTriangle_comp comm A B D)
    (paddedTriangle_distinguished _ h₁ A B)
    (paddedTriangle_distinguished _ h₂ B D)
    (paddedTriangle_distinguished _ h₃ A D))

lemma paddedOctahedron_first_inr :
    ((biprod.inr : B ⟶ U ⊞ B) ≫ biprod.inl) ≫ H.m₁ = 0 := by
  have he := (biprod.inr : B ⟶ Y ⊞ B) ≫= H.comm₁
  simpa [paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc] using he

lemma paddedOctahedron_first_snd : H.m₁ ≫ biprod.snd = biprod.snd := by
  have he := H.comm₂ =≫ (shiftFunctor C (1 : ℤ)).map (biprod.snd : X ⊞ A ⟶ A)
  simpa [paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc,
    ← CategoryTheory.Functor.map_comp, biprodDescComp, biprod.desc_eq, add_comp] using he

lemma paddedOctahedron_second_inr :
    ((biprod.inr : D ⟶ W ⊞ D) ≫ biprod.inl) ≫ H.m₃ =
      (biprod.inr : D ⟶ V ⊞ D) ≫ biprod.inl := by
  have he := (biprod.inr : D ⟶ Z ⊞ D) ≫= H.comm₃
  simpa [paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc] using he

lemma paddedOctahedron_second_snd : H.m₃ ≫ biprod.snd = 0 := by
  have he := H.comm₄ =≫ (shiftFunctor C (1 : ℤ)).map (biprod.snd : Y ⊞ B ⟶ B)
  simpa [paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc,
    ← CategoryTheory.Functor.map_comp, biprodDescComp, biprod.desc_eq, add_comp] using he.symm

/-- 大きい八面体の第三の射は、主成分と自明な成分のブロック和。 -/
lemma paddedOctahedron_third :
    (paddedTriangle (Triangle.mk v c d) B D).mor₃ ≫
      (shiftFunctor C (1 : ℤ)).map (paddedTriangle (Triangle.mk u a b) A B).mor₂ =
        octahedronBlockThird (A := A⟦(1 : ℤ)⟧) (B := B) (D := D)
          (d ≫ (shiftFunctor C (1 : ℤ)).map a) := by
  dsimp [paddedTriangle, triangleAddSource, triangleAddTarget, octahedronBlockThird]
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    all_goals simp [Category.assoc, ← CategoryTheory.Functor.map_comp]
  · simp [Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- 大きい八面体から四つの可換条件と直和因子の三角形を取り出す。 -/
def octahedronOfPadding
    (hretract : ∀ (T S : Triangle C), S ∈ distTriang C → Retract T S → T ∈ distTriang C) :
    Octahedron comm h₁ h₂ h₃ := by
  let F := H.m₁
  let G := H.m₃
  let F₁ : U ⟶ W := biprod.inl ≫ biprod.inl ≫ F ≫ biprod.fst ≫ biprod.fst
  let G₁ : W ⟶ V := biprod.inl ≫ biprod.inl ≫ G ≫ biprod.fst ≫ biprod.fst
  refine ⟨F₁, G₁, ?_, ?_, ?_, ?_, ?_⟩
  · have he := (biprod.inl : Y ⟶ Y ⊞ B) ≫= H.comm₁ =≫
      (biprod.fst ≫ (biprod.fst : W ⊞ D ⟶ W))
    simpa [F₁, F, paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc] using he
  · have he := ((biprod.inl : U ⟶ U ⊞ B) ≫ biprod.inl) ≫= H.comm₂ =≫
      (shiftFunctor C (1 : ℤ)).map (biprod.fst : X ⊞ A ⟶ X)
    simpa [F₁, F, paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc,
      ← CategoryTheory.Functor.map_comp, biprodDescComp, biprod.desc_eq,
      add_comp, comp_add] using he
  · have he := (biprod.inl : Z ⟶ Z ⊞ D) ≫= H.comm₃ =≫
      (biprod.fst ≫ (biprod.fst : V ⊞ D ⟶ V))
    simpa [G₁, G, paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc] using he
  · have he := ((biprod.inl : W ⟶ W ⊞ D) ≫ biprod.inl) ≫= H.comm₄ =≫
      (shiftFunctor C (1 : ℤ)).map (biprod.fst : Y ⊞ B ⟶ Y)
    simpa [G₁, G, paddedTriangle, triangleAddSource, triangleAddTarget, Category.assoc,
      ← CategoryTheory.Functor.map_comp, biprodDescComp, biprod.desc_eq,
      add_comp, comp_add] using he
  · have hF := octahedronBlockFirst_eq F
      (paddedOctahedron_first_inr comm h₁ h₂ h₃ A B D H)
      (paddedOctahedron_first_snd comm h₁ h₂ h₃ A B D H)
    have hG := octahedronBlockSecond_eq G
      (paddedOctahedron_second_inr comm h₁ h₂ h₃ A B D H)
      (paddedOctahedron_second_snd comm h₁ h₂ h₃ A B D H)
    have hfg : F ≫ G = 0 := comp_distTriang_mor_zero₁₂ _ H.mem
    rw [hF, hG] at hfg
    have r := octahedronBlockRetract _ _ _ _ _ _ _ _
      (d ≫ (shiftFunctor C (1 : ℤ)).map a) hfg
    apply hretract _ _ H.mem
    rw [← hF, ← hG, ← paddedOctahedron_third (u := u) (a := a) (b := b)
      (v := v) (c := c) (d := d) A B D] at r
    exact r

end

end SerrePositivity
