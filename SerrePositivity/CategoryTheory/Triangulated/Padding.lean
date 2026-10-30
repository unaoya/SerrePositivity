module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # 完全三角形と八面体への自明な因子の付け加え

## 概要

二つの完全三角形の直和が完全であること、自明な三角形を加えても完全であること、自明な因子を加えた八面体から元の八面体への降下、完全忠実な三角関手の本質像上の八面体を与える。

## 方針

直和の完全性は Mathlib の `productTriangle_distinguished`（積の三角形）から導く。降下は自明な直和因子を retract で取り除く（Balmer–Schlichting の八面体のブロック形）。

## 規約

本質像の八面体は、完全忠実性で射を引き戻して示す。

## 使われ方

Karoubi 包絡の八面体公理（`Karoubi/Triangulated`）、DifferentialGraded の比較。
-/

@[expose] public noncomputable section

section TriangleBiproductPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

@[reassoc]
lemma biprodDescComp {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext' <;> simp

/-- 三頂点に二項直和を使った三角形。 -/
@[simps!]
def triangleBiproduct (T U : Triangle C) : Triangle C :=
  Triangle.mk (biprod.map T.mor₁ U.mor₁) (biprod.map T.mor₂ U.mor₂)
    (biprod.desc (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
      (U.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inr))

@[simps]
def triangleBiproductFst (T U : Triangle C) : triangleBiproduct T U ⟶ T where
  hom₁ := biprod.fst
  hom₂ := biprod.fst
  hom₃ := biprod.fst
  comm₁ := by simp [triangleBiproduct]
  comm₂ := by simp [triangleBiproduct]
  comm₃ := by
    dsimp [triangleBiproduct]
    apply biprod.hom_ext'
    all_goals simp [← CategoryTheory.Functor.map_comp]

@[simps]
def triangleBiproductSnd (T U : Triangle C) : triangleBiproduct T U ⟶ U where
  hom₁ := biprod.snd
  hom₂ := biprod.snd
  hom₃ := biprod.snd
  comm₁ := by simp [triangleBiproduct]
  comm₂ := by simp [triangleBiproduct]
  comm₃ := by
    dsimp [triangleBiproduct]
    apply biprod.hom_ext'
    all_goals simp [← CategoryTheory.Functor.map_comp]

/-- 二項直和から Bool で添字づけた積への標準射は同型。 -/
lemma isIso_biprod_to_bool_product (X : Bool → C) :
    IsIso (Pi.lift (fun b : Bool ↦ Bool.rec
      (biprod.fst : X false ⊞ X true ⟶ X false) biprod.snd b)) := by
  let f := Pi.lift (fun b : Bool ↦ Bool.rec
    (biprod.fst : X false ⊞ X true ⟶ X false) biprod.snd b)
  refine ⟨⟨biprod.lift (Pi.π X false) (Pi.π X true), ?_, ?_⟩⟩
  · apply biprod.hom_ext
    all_goals simp
  · apply Pi.hom_ext
    intro b
    cases b <;> simp

lemma triangleBiproduct_distinguished (T U : Triangle C)
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C) :
    triangleBiproduct T U ∈ distTriang C := by
  let V : Bool → Triangle C := Bool.rec T U
  let f := productTriangle.lift V (Bool.rec (triangleBiproductFst T U)
    (triangleBiproductSnd T U))
  have h₁ : IsIso f.hom₁ := by
    have he : f.hom₁ = Pi.lift (f := fun b ↦ (V b).obj₁) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₁ ⊞ U.obj₁ ⟶ (V b).obj₁) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₁)
  have h₂ : IsIso f.hom₂ := by
    have he : f.hom₂ = Pi.lift (f := fun b ↦ (V b).obj₂) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₂ ⊞ U.obj₂ ⟶ (V b).obj₂) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₂)
  have h₃ : IsIso f.hom₃ := by
    have he : f.hom₃ = Pi.lift (f := fun b ↦ (V b).obj₃) (fun b : Bool ↦ Bool.rec
        (motive := fun b ↦ T.obj₃ ⊞ U.obj₃ ⟶ (V b).obj₃) biprod.fst biprod.snd b) := by
      apply Pi.hom_ext
      intro b
      cases b <;> simp [f]
    rw [he]
    exact isIso_biprod_to_bool_product (fun b ↦ (V b).obj₃)
  have : IsIso f := Triangle.isIso_of_isIsos f h₁ h₂ h₃
  exact isomorphic_distinguished _ (productTriangle_distinguished V
    (by intro b; cases b <;> assumption)) _ (asIso f)

end

end SerrePositivity

end TriangleBiproductPart

section TrianglePaddingPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive
open scoped ZeroObject

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

@[simps!]
def triangleAddTarget (T : Triangle C) (B : C) : Triangle C :=
  Triangle.mk (T.mor₁ ≫ (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ B))
    (biprod.map T.mor₂ (𝟙 B)) (biprod.fst ≫ T.mor₃)

lemma triangleAddTarget_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (B : C) :
    triangleAddTarget T B ∈ distTriang C := by
  let U := Triangle.mk (0 : 0 ⟶ B) (𝟙 B) 0
  refine isomorphic_distinguished _
    (triangleBiproduct_distinguished T U hT (contractible_distinguished₁ B)) _ ?_
  refine Triangle.isoMk _ _ (isoBiprodZero (isZero_zero C)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [triangleAddTarget, triangleBiproduct, U]
  · simp [triangleAddTarget, triangleBiproduct, U]
  · dsimp [triangleAddTarget, triangleBiproduct, U]
    apply biprod.hom_ext'
    all_goals simp

@[simps!]
def triangleAddSource (T : Triangle C) (A : C) : Triangle C :=
  Triangle.mk ((biprod.fst : T.obj₁ ⊞ A ⟶ T.obj₁) ≫ T.mor₁)
    (T.mor₂ ≫ biprod.inl)
    (biprod.desc (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
      ((shiftFunctor C (1 : ℤ)).map biprod.inr))

lemma triangleAddSource_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (A : C) :
    triangleAddSource T A ∈ distTriang C := by
  let U := Triangle.mk (0 : A ⟶ 0) 0 (𝟙 (A⟦(1 : ℤ)⟧))
  refine isomorphic_distinguished _
    (triangleBiproduct_distinguished T U hT (contractible_distinguished₂ A)) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (isoBiprodZero (isZero_zero C)) (Iso.refl _)
    ?_ ?_ ?_
  · dsimp [triangleAddSource, triangleBiproduct, U]
    apply biprod.hom_ext'
    all_goals simp
  · simp [triangleAddSource, triangleBiproduct, U]
  · simp [triangleAddSource, triangleBiproduct, U]

/-- 両端の対象を直和で拡大し、錐に自明な因子を加えた三角形。 -/
@[simps!]
def paddedTriangle (T : Triangle C) (A B : C) : Triangle C :=
  triangleAddSource (triangleAddTarget T B) A

lemma paddedTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (A B : C) :
    paddedTriangle T A B ∈ distTriang C :=
  triangleAddSource_distinguished _ (triangleAddTarget_distinguished T hT B) A

end

end SerrePositivity

end TrianglePaddingPart

section OctahedronBlockRetractPart

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

end OctahedronBlockRetractPart

section OctahedronPaddingPart

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

end OctahedronPaddingPart

section OctahedronEssentialImagePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ] [F.IsTriangulated]

omit [F.Faithful] in
/-- 合成する二つの射の三頂点が本質像にあれば、元の圏の八面体を移せる。 -/
lemma nonempty_octahedron_of_essImage
    {X Y Z U V W : D} {u : X ⟶ Y} {v : Y ⟶ Z} {w : X ⟶ Z}
    (comm : u ≫ v = w)
    {a : Y ⟶ U} {b : U ⟶ X⟦(1 : ℤ)⟧} (h₁ : Triangle.mk u a b ∈ distTriang D)
    {c : Z ⟶ V} {d : V ⟶ Y⟦(1 : ℤ)⟧} (h₂ : Triangle.mk v c d ∈ distTriang D)
    {e : Z ⟶ W} {f : W ⟶ X⟦(1 : ℤ)⟧} (h₃ : Triangle.mk w e f ∈ distTriang D)
    (hX : F.essImage X) (hY : F.essImage Y) (hZ : F.essImage Z) :
    Nonempty (Octahedron comm h₁ h₂ h₃) := by
  obtain ⟨X', ⟨iX⟩⟩ := hX
  obtain ⟨Y', ⟨iY⟩⟩ := hY
  obtain ⟨Z', ⟨iZ⟩⟩ := hZ
  let u' := F.preimage (iX.hom ≫ u ≫ iY.inv)
  let v' := F.preimage (iY.hom ≫ v ≫ iZ.inv)
  obtain ⟨_, _, _, h₁'⟩ := distinguished_cocone_triangle u'
  obtain ⟨_, _, _, h₂'⟩ := distinguished_cocone_triangle v'
  obtain ⟨_, _, _, h₃'⟩ := distinguished_cocone_triangle (u' ≫ v')
  exact ⟨Octahedron.ofIso (e₁ := iX.symm) (e₂ := iY.symm) (e₃ := iZ.symm)
    (comm₁₂ := by simp [u']) (comm₂₃ := by simp [v'])
    (H := (someOctahedron rfl h₁' h₂' h₃').map F) ..⟩

end SerrePositivity

end OctahedronEssentialImagePart
