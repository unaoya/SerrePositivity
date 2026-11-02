module

public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.Spectra.SymmetricSequence.FreeConvolutionDesc

/-! # 自由convolutionの誘導図式による表示

第二ブロックをnに固定し、第一ブロックの作用による同一視を余極限で表す。
生成元上の関係式と降下の普遍性から、各段との比較同型を構成する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C]

/-- 第二ブロックをnに固定した誘導図式。 -/
def freeInductionDiagram (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m) ⥤ C :=
  CostructuredArrow.proj _ _ ⋙ toFunctorCategory.obj F ⋙ tensorRight X

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 誘導図式の第一ブロックの濃度はm−nに決まる。 -/
lemma freeInduction_card (n m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    FiniteBijection.card d.left = m - n := by
  have h : FiniteBijection.card d.left + n = m := FiniteBijection.card_eq_of_hom d.hom
  omega

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 誘導図式の各項は、次数m−nの段と入力のテンソル積。 -/
lemma freeInductionDiagram_obj (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    (freeInductionDiagram F n X m).obj d = F.obj (FiniteBijection.of (m - n)) ⊗ X := by
  change F.obj d.left ⊗ X = _
  have h : d.left = FiniteBijection.of (m - n) := by
    rw [← FiniteBijection.of_card d.left, freeInduction_card n m d]
  rw [h]

/-- 射の決定には第一ブロックm−nの生成元だけで十分。 -/
lemma freeConvolutionLevel_hom_ext_standard (F : SymmetricSequence C) (n : ℕ) (X : C)
    (m : ℕ) {Y : C} (f g : level (convolution F ((freeAt n).obj X)) m ⟶ Y)
    (h : ∀ k : FiniteBijection.sumObj (FiniteBijection.of (m - n))
        (FiniteBijection.of n) ⟶ FiniteBijection.of m,
      freeConvolutionGenerator F n X m (FiniteBijection.of (m - n)) k ≫ f =
        freeConvolutionGenerator F n X m (FiniteBijection.of (m - n)) k ≫ g) : f = g := by
  apply freeConvolutionLevel_hom_ext
  intro a k
  have ha : a = FiniteBijection.of (m - n) := by
    have hc : FiniteBijection.card a = m - n :=
      freeInduction_card n m (CostructuredArrow.mk (Y := a) k)
    exact (FiniteBijection.of_card a).symm.trans (congrArg FiniteBijection.of hc)
  subst a
  exact h k

/-- 誘導図式の余錐を、関係式を満たす射の族として読む。 -/
def freeInductionFamily (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (c : Cocone (freeInductionDiagram F n X m)) : FreeConvolutionFamily F n X m c.pt where
  app a h := c.ι.app (CostructuredArrow.mk (Y := a) h)
  relation {a b} k h := by
    let d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m) :=
      CostructuredArrow.mk (Y := a) (FiniteBijection.sumMap k (𝟙 _) ≫ h)
    let e : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m) :=
      CostructuredArrow.mk (Y := b) h
    let φ : d ⟶ e := CostructuredArrow.homMk k (by rfl)
    exact c.w φ

/-- 各段の生成元は誘導図式上の余錐を作る。 -/
def freeInductionCocone (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    Cocone (freeInductionDiagram F n X m) where
  pt := level (convolution F ((freeAt n).obj X)) m
  ι.app d := freeConvolutionGenerator F n X m d.left d.hom
  ι.naturality d e φ := by
    change F.map φ.left ▷ X ≫ freeConvolutionGenerator F n X m e.left e.hom =
      freeConvolutionGenerator F n X m d.left d.hom ≫ 𝟙 _
    erw [Category.comp_id, freeConvolutionGenerator_left_relation]
    have h := CostructuredArrow.w φ
    change FiniteBijection.sumMap φ.left (𝟙 (FiniteBijection.of n)) ≫ e.hom = d.hom at h
    exact congrArg (freeConvolutionGenerator F n X m d.left) h

/-- 各段は誘導図式の余極限の普遍性を持つ。 -/
def freeInductionCoconeIsColimit (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    IsColimit (freeInductionCocone F n X m) where
  desc c := (freeInductionFamily F n X m c).desc
  fac c d := (freeInductionFamily F n X m c).desc_fac d.left d.hom
  uniq c f h := by
    apply freeConvolutionLevel_hom_ext
    intro a k
    erw [FreeConvolutionFamily.desc_fac]
    exact h (CostructuredArrow.mk (Y := a) k)

/-- 自由convolutionの第m段は、第一ブロックに沿う誘導図式の余極限。 -/
def freeConvolutionLevelIsoInduction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    level (convolution F ((freeAt n).obj X)) m ≅ colimit (freeInductionDiagram F n X m) :=
  (freeInductionCoconeIsColimit F n X m).coconePointUniqueUpToIso (colimit.isColimit _)

/-- 誘導表示の比較同型は生成元を標準包含へ送る。 -/
@[reassoc (attr := simp)] lemma freeConvolutionLevelIsoInduction_generator
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    freeConvolutionGenerator F n X m d.left d.hom ≫
      (freeConvolutionLevelIsoInduction F n X m).hom =
        colimit.ι (freeInductionDiagram F n X m) d :=
  (freeInductionCoconeIsColimit F n X m).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) d

/-- 誘導表示の逆同型は標準包含を各段の生成元へ戻す。 -/
@[reassoc (attr := simp)] lemma freeConvolutionLevelIsoInduction_inclusion
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeInductionDiagram F n X m) d ≫
      (freeConvolutionLevelIsoInduction F n X m).inv =
        freeConvolutionGenerator F n X m d.left d.hom := by
  rw [← freeConvolutionLevelIsoInduction_generator, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end SerrePositivity.SymmetricSequence
