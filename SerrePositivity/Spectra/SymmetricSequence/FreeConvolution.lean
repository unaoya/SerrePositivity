module

public import SerrePositivity.CategoryTheory.Limits.InitialColimits
public import SerrePositivity.Spectra.SymmetricSequence.FreeSupport
public import SerrePositivity.Spectra.SymmetricSequence.Convolution
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # 自由対称列とのconvolutionの次数

第n段を生成する自由対称列とのconvolutionの各段を、分解図式の余極限で表す。
m<nの場合は全ての項が始対象となり、その余極限も始対象となる。
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

/-- 自由対称列とのconvolutionの具体的な分解図式。 -/
def freeConvolutionDiagram (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m) ⥤ C :=
  decompositionDiagram F ((freeAt n).obj X) m

omit [MonoidalClosed C] in
/-- 分解の各項は、全単射で添字付けた余積とのテンソル積。 -/
lemma freeConvolutionDiagram_obj (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)) :
    (freeConvolutionDiagram F n X m).obj d = F.obj d.left.1 ⊗
      ∐ (fun _ : FiniteBijection.of n ⟶ d.left.2 => X) := rfl

/-- 自由対称列とのconvolutionの各段の余極限表示。 -/
def freeConvolutionLevelIsoColimit (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    level (convolution F ((freeAt n).obj X)) m ≅ colimit (freeConvolutionDiagram F n X m) :=
  convolutionLevelIsoColimit F ((freeAt n).obj X) m

/-- 第m段の生成元。aとnの直和からmへの全単射で添字付ける。 -/
def freeConvolutionGenerator (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (a : FiniteBijection) (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶
      FiniteBijection.of m) : F.obj a ⊗ X ⟶ level (convolution F ((freeAt n).obj X)) m :=
  F.obj a ◁ freeAtGenerator n X ≫
    (convolutionUnit F ((freeAt n).obj X)).app (a, FiniteBijection.of n) ≫
      (convolution F ((freeAt n).obj X)).map h

omit [MonoidalClosed C] in
/-- 分解項の余積成分からの射も、上の生成元に一致する。 -/
@[reassoc] lemma freeConvolutionGenerator_eq (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m))
    (k : FiniteBijection.of n ⟶ d.left.2) :
    F.obj d.left.1 ◁ freeAtInclusion n X k ≫
      (convolutionUnit F ((freeAt n).obj X)).app d.left ≫
        (convolution F ((freeAt n).obj X)).map d.hom =
    freeConvolutionGenerator F n X m d.left.1
      (FiniteBijection.sumMap (𝟙 d.left.1) k ≫ d.hom) := by
  have hn := (convolutionUnit F ((freeAt n).obj X)).naturality
    (show (d.left.1, FiniteBijection.of n) ⟶ d.left from (𝟙 _, k))
  change ((F.map (𝟙 _) ▷ _) ≫ (F.obj d.left.1 ◁ ((freeAt n).obj X).map k)) ≫
    (convolutionUnit F ((freeAt n).obj X)).app d.left =
      (convolutionUnit F ((freeAt n).obj X)).app (d.left.1, FiniteBijection.of n) ≫
        (convolution F ((freeAt n).obj X)).map (FiniteBijection.sumMap (𝟙 _) k) at hn
  simp only [CategoryTheory.Functor.map_id, id_whiskerRight, Category.id_comp] at hn
  erw [← freeAtInclusion_eq_generator n X k, whiskerLeft_comp, Category.assoc,
    reassoc_of% hn]
  simp only [freeConvolutionGenerator, CategoryTheory.Functor.map_comp]

omit [MonoidalClosed C] in
/-- 出力の全単射は、生成元の添字に後合成する。 -/
@[reassoc] lemma freeConvolutionGenerator_map (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m m' : ℕ) (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m)
    (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    freeConvolutionGenerator F n X m a h ≫ (convolution F ((freeAt n).obj X)).map k =
      freeConvolutionGenerator F n X m' a (h ≫ k) := by
  simp only [freeConvolutionGenerator, CategoryTheory.Functor.map_comp, Category.assoc]

omit [MonoidalClosed C] in
/-- 第一ブロックの全単射による作用と、生成元の添字の同一視の関係。 -/
@[reassoc] lemma freeConvolutionGenerator_left_relation (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) {a b : FiniteBijection} (k : a ⟶ b)
    (h : FiniteBijection.sumObj b (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    F.map k ▷ X ≫ freeConvolutionGenerator F n X m b h =
      freeConvolutionGenerator F n X m a
        (FiniteBijection.sumMap k (𝟙 (FiniteBijection.of n)) ≫ h) := by
  have hn := (convolutionUnit F ((freeAt n).obj X)).naturality
    (show (a, FiniteBijection.of n) ⟶ (b, FiniteBijection.of n) from (k, 𝟙 _))
  change ((F.map k ▷ _) ≫ (F.obj b ◁ ((freeAt n).obj X).map (𝟙 _))) ≫
    (convolutionUnit F ((freeAt n).obj X)).app (b, FiniteBijection.of n) =
      (convolutionUnit F ((freeAt n).obj X)).app (a, FiniteBijection.of n) ≫
        (convolution F ((freeAt n).obj X)).map
          (FiniteBijection.sumMap k (𝟙 (FiniteBijection.of n))) at hn
  simp only [CategoryTheory.Functor.map_id, whiskerLeft_id, Category.comp_id] at hn
  simp only [freeConvolutionGenerator]
  erw [← whisker_exchange_assoc, reassoc_of% hn]
  rw [CategoryTheory.Functor.map_comp]

/-- 各段からの射は、直和の全単射で添字付けた生成元上の値で決まる。 -/
lemma freeConvolutionLevel_hom_ext (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    {Y : C} (f g : level (convolution F ((freeAt n).obj X)) m ⟶ Y)
    (h : ∀ (a : FiniteBijection)
      (k : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m),
      freeConvolutionGenerator F n X m a k ≫ f =
        freeConvolutionGenerator F n X m a k ≫ g) : f = g := by
  apply (cancel_epi (freeConvolutionLevelIsoColimit F n X m).inv).1
  apply colimit.hom_ext
  intro d
  change colimit.ι (freeConvolutionDiagram F n X m) d ≫
    (convolutionLevelIsoColimit F ((freeAt n).obj X) m).inv ≫ f =
      colimit.ι (freeConvolutionDiagram F n X m) d ≫
        (convolutionLevelIsoColimit F ((freeAt n).obj X) m).inv ≫ g
  erw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
  erw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
  apply (isColimitOfPreserves (tensorLeft (F.obj d.left.1))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ d.left.2 => X)))).hom_ext
  intro k
  change (F.obj d.left.1 ◁ freeAtInclusion n X k.as) ≫
    ((convolutionUnit F ((freeAt n).obj X)).app d.left ≫
      (convolution F ((freeAt n).obj X)).map d.hom ≫ f) =
    (F.obj d.left.1 ◁ freeAtInclusion n X k.as) ≫
    ((convolutionUnit F ((freeAt n).obj X)).app d.left ≫
      (convolution F ((freeAt n).obj X)).map d.hom ≫ g)
  erw [freeConvolutionGenerator_eq_assoc, freeConvolutionGenerator_eq_assoc]
  exact h d.left.1 (FiniteBijection.sumMap (𝟙 d.left.1) k.as ≫ d.hom)

/-- m<nの場合、各分解項は始対象になる。 -/
def freeConvolutionDiagramObjInitial (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : m < n)
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)) :
    IsInitial ((freeConvolutionDiagram F n X m).obj d) := by
  have hq : n ≠ FiniteBijection.card d.left.2 := by
    have hd := decomposition_card m d
    omega
  exact (freeAtObjInitial n X d.left.2 hq).isInitialObj (tensorLeft (F.obj d.left.1)) _

/-- 第n段の自由対称列とのconvolutionはn未満の段で始対象。 -/
def freeConvolutionLevelInitial (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : m < n) : IsInitial (level (convolution F ((freeAt n).obj X)) m) :=
  (colimitOfInitialsIsInitial (freeConvolutionDiagram F n X m)
    (freeConvolutionDiagramObjInitial F n X m hm)).ofIso
      (freeConvolutionLevelIsoColimit F n X m).symm

end SerrePositivity.SymmetricSequence
