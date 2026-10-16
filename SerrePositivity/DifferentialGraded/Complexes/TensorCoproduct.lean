module
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 二つの複体の余積からのtensor写像の普遍性

余積とtensorの交換を既存閉構造の随伴から得る。添字の宇宙をHomの宇宙へ固定せず、
指定した余積の存在を仮定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable {A : Type u} [CommRing A] {I : Type v} {J : Type w}

/-- 左tensorは指定された複体余積のcofanを余積へ送る。 -/
def tensorLeftCoproductIsColimit (K : Complex A) (F : I → Complex A) [HasCoproduct F] :
    IsColimit (Cofan.mk (K ⊗ ∐ F) (fun i => K ◁ Sigma.ι F i)) :=
  isColimitOfHasCoproductOfPreservesColimit (tensorLeft K) F

/-- 右tensorの余積保存は既存の右tensor–Hom随伴から得る。 -/
def tensorRightCoproductIsColimit (K : Complex A) (F : I → Complex A) [HasCoproduct F] :
    IsColimit (Cofan.mk ((∐ F) ⊗ K) (fun i => Sigma.ι F i ▷ K)) := by
  letI := (tensorRightHomAdjunction K).isLeftAdjoint
  exact isColimitOfHasCoproductOfPreservesColimit (tensorRight K) F

/-- 一つの因子を固定した右余積からのtensor写像。 -/
def tensorCoproductRightDesc (K : Complex A) (G : J → Complex A) [HasCoproduct G]
    (T : Complex A) (f : ∀ j, K ⊗ G j ⟶ T) : K ⊗ ∐ G ⟶ T :=
  (tensorLeftCoproductIsColimit K G).desc (Cofan.mk T f)

lemma tensorCoproductRightDesc_ι (K : Complex A) (G : J → Complex A) [HasCoproduct G]
    (T : Complex A) (f : ∀ j, K ⊗ G j ⟶ T) (j : J) :
    (K ◁ Sigma.ι G j) ≫ tensorCoproductRightDesc K G T f = f j :=
  (tensorLeftCoproductIsColimit K G).fac (Cofan.mk T f) ⟨j⟩

/-- 各二因子上の写像を二つの余積のtensorへ延長する。 -/
def tensorCoproductDesc (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T) :
    (∐ F) ⊗ (∐ G) ⟶ T :=
  (tensorRightCoproductIsColimit (∐ G) F).desc
    (Cofan.mk T (fun i => tensorCoproductRightDesc (F i) G T (f i)))

lemma tensorCoproductDesc_left (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T) (i : I) :
    (Sigma.ι F i ▷ ∐ G) ≫ tensorCoproductDesc F G T f =
      tensorCoproductRightDesc (F i) G T (f i) :=
  (tensorRightCoproductIsColimit (∐ G) F).fac
    (Cofan.mk T (fun i => tensorCoproductRightDesc (F i) G T (f i))) ⟨i⟩

lemma tensorCoproductDesc_ι (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] (T : Complex A) (f : ∀ i j, F i ⊗ G j ⟶ T)
    (i : I) (j : J) :
    (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ tensorCoproductDesc F G T f = f i j := by
  rw [tensorHom_def', Category.assoc, tensorCoproductDesc_left, tensorCoproductRightDesc_ι]

/-- 二つの余積のtensorからのchain mapは各二因子への制限で決まる。 -/
lemma tensorCoproduct_hom_ext (F : I → Complex A) (G : J → Complex A)
    [HasCoproduct F] [HasCoproduct G] {T : Complex A} (f g : (∐ F) ⊗ (∐ G) ⟶ T)
    (h : ∀ i j, (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ f =
      (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ g) : f = g := by
  apply (tensorRightCoproductIsColimit (∐ G) F).hom_ext
  rintro ⟨i⟩
  apply (tensorLeftCoproductIsColimit (F i) G).hom_ext
  rintro ⟨j⟩
  change (F i ◁ Sigma.ι G j) ≫ (Sigma.ι F i ▷ ∐ G) ≫ f =
    (F i ◁ Sigma.ι G j) ≫ (Sigma.ι F i ▷ ∐ G) ≫ g
  simpa only [← Category.assoc, ← tensorHom_def'] using h i j

end SerrePositivity.DifferentialGraded
