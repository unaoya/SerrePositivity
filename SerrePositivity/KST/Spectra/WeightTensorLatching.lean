module

public import SerrePositivity.KST.Spectra.BousfieldKanWeightLatching
public import SerrePositivity.KST.Spectra.BoundaryTensorMonomorphism
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：任意の余単体重みとパラメーターの射の相対 latching の pushout-product 表示。
方針：右 tensor による latching 余極限の保存と、その自然性で実際の pushout を比較する。
規約：モデル圏構造を仮定せず、実際の arrow 同型を与える。
使われ方：Goerss–Jardine VII §4。重みの cylinder と通常 Tot 比較の相対持ち上げ。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.WeightTensorLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F : CosimplicialObject SSet.{u})

/-- 任意の重みの各段にパラメーターを tensor した図式。 -/
abbrev diagram (A : SSet.{u}) : CosimplicialObject SSet.{u} := F ⋙ tensorRight A

/-- パラメーターの射を各段で tensor した自然変換。 -/
def map {A B : SSet.{u}} (i : A ⟶ B) : diagram F A ⟶ diagram F B where
  app j := F.obj j ◁ i
  naturality _ _ g := whisker_exchange (F.map g) i

/-- tensor と latching 余極限の交換の標準同型。 -/
def iso (A : SSet.{u}) (j : SimplexCategory) :
    (latchingEvaluation simplex j).obj (diagram F A) ≅
      (latchingEvaluation simplex j).obj F ⊗ A :=
  (preservesColimitIso (tensorRight A) (latchingSource simplex j ⋙ F)).symm

/-- 交換同型の後で latching 射を tensor すると元の latching 射。 -/
lemma iso_comparison (A : SSet.{u}) (j : SimplexCategory) :
    (iso F A j).hom ≫ ((latchingComparison simplex j).app F ▷ A) =
      (latchingComparison simplex j).app (diagram F A) := by
  change (preservesColimitIso (tensorRight A) (latchingSource simplex j ⋙ F)).inv ≫
    (tensorRight A).map (colimit.desc _ (latchingCocone simplex F j)) = _
  rw [preservesColimitIso_inv_comp_desc]
  rfl

/-- latching 余極限と tensor の交換はパラメーターの射に自然。 -/
lemma iso_natural {A B : SSet.{u}} (i : A ⟶ B) (j : SimplexCategory) :
    (latchingEvaluation simplex j).map (map F i) ≫ (iso F B j).hom =
      (iso F A j).hom ≫ ((latchingEvaluation simplex j).obj F ◁ i) := by
  change colim.map (Functor.whiskerLeft (latchingSource simplex j) (map F i)) ≫ _ = _
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, colimit.ι_map, Category.assoc]
  change (F.obj a.obj.left ◁ i) ≫
    (colimit.ι ((latchingSource simplex j ⋙ F) ⋙ tensorRight B) a ≫
    (preservesColimitIso (tensorRight B) (latchingSource simplex j ⋙ F)).inv) =
    colimit.ι ((latchingSource simplex j ⋙ F) ⋙ tensorRight A) a ≫
      (preservesColimitIso (tensorRight A)
      (latchingSource simplex j ⋙ F)).inv ≫ _
  rw [ι_preservesColimitIso_inv, ι_preservesColimitIso_inv_assoc]
  exact (whisker_exchange (colimit.ι (latchingSource simplex j ⋙ F) a) i).symm

variable {A B : SSet.{u}} (i : A ⟶ B) (j : SimplexCategory)

/-- latching 射とパラメーターの射の実際の pushout-product の正方形。 -/
def productSquare : (curriedTensor SSet.{u}).PushoutObjObj
    ((latchingComparison simplex j).app F) i where
  pt := pushout ((latchingEvaluation simplex j).obj F ◁ i)
    ((latchingComparison simplex j).app F ▷ A)
  inl := pushout.inr _ _
  inr := pushout.inl _ _
  isPushout := (IsPushout.of_hasPushout
    ((latchingEvaluation simplex j).obj F ◁ i)
    ((latchingComparison simplex j).app F ▷ A)).flip

/-- 二つの latching の交換同型から相対押し出しの比較射を作る。 -/
abbrev relativeProductMap :=
  pushout.map ((latchingEvaluation simplex j).map (map F i))
    ((latchingComparison simplex j).app (diagram F A))
    ((latchingEvaluation simplex j).obj F ◁ i)
    ((latchingComparison simplex j).app F ▷ A)
    (iso F B j).hom (𝟙 _) (iso F A j).hom (iso_natural F i j)
    ((Category.comp_id _).trans (iso_comparison F A j).symm)

instance relativeProductMap_isIso : IsIso (relativeProductMap F i j) :=
  pushout.map_isIso _ _ _ _ (iso F B j).hom (𝟙 _) (iso F A j).hom _ _

/-- パラメーターの射の相対 latching は重みの latching 射との pushout-product。 -/
def relativeProductArrowIso :
    Arrow.mk (relativeLatchingMap simplex j (map F i)) ≅
      Arrow.mk (productSquare F i j).ι := by
  refine Arrow.isoMk (asIso (relativeProductMap F i j)) (Iso.refl _) ?_
  change relativeProductMap F i j ≫ (productSquare F i j).ι = _ ≫ 𝟙 _
  rw [Category.comp_id]
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, Category.assoc]
    change (iso F B j).hom ≫ (productSquare F i j).inr ≫ _ = _
    rw [Functor.PushoutObjObj.inr_ι]
    change (iso F B j).hom ≫ ((latchingComparison simplex j).app F ▷ B) = _
    rw [iso_comparison]
    exact (inl_relativeLatchingMap simplex j (map F i)).symm
  · rw [← Category.assoc, pushout.inr_desc, Category.id_comp]
    change (productSquare F i j).inl ≫ _ = _
    rw [Functor.PushoutObjObj.inl_ι]
    exact (inr_relativeLatchingMap simplex j (map F i)).symm

end
end SerrePositivity.KST.Spectra.WeightTensorLatching
