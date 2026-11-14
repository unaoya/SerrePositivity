module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Monoidal model compatibility and the separate unit axiom

These are properties of the existing monoidal category and model structure.
The unit need not be cofibrant: the unit axiom specifies a cofibrant replacement
and requires its left and right tensor maps on cofibrant objects to be weak
equivalences. It is not inferred from the pushout-product condition.
-/

@[expose] public section

universe u v

open CategoryTheory HomotopicalAlgebra CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- The unit axiom for a specified replacement of the monoidal unit. -/
structure UnitReplacementAxiom (Q : C) (q : Q ⟶ 𝟙_ C) : Prop where
  cofibrant : IsCofibrant Q
  weakEquivalence : WeakEquivalence q
  left (X : C) : IsCofibrant X → WeakEquivalence (q ▷ X)
  right (X : C) : IsCofibrant X → WeakEquivalence (X ◁ q)

/-- Existence of a replacement satisfying the unit axiom, independently of
the pushout-product condition. -/
class HasUnitAxiom : Prop where
  exists_replacement : ∃ (Q : C) (q : Q ⟶ 𝟙_ C), UnitReplacementAxiom C Q q

/-- A monoidal model category is the existing model and monoidal structures
with pushout-product compatibility and the separate unit axiom. -/
class MonoidalModelCategory : Prop where
  pushoutProduct : IsQuillenBifunctor (curriedTensor C)
  unit : HasUnitAxiom C

attribute [instance] MonoidalModelCategory.pushoutProduct MonoidalModelCategory.unit

/-- A cofibrant unit satisfies the unit axiom using its identity replacement. -/
lemma unitAxiom_of_cofibrant_unit [IsCofibrant (𝟙_ C)] : HasUnitAxiom C := by
  refine ⟨𝟙_ C, 𝟙 _, ?_⟩
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro X _
    simp only [MonoidalCategory.id_whiskerRight]
    infer_instance
  · intro X _
    simp only [MonoidalCategory.whiskerLeft_id]
    infer_instance

variable [MonoidalClosed C]

/-- The closed monoidal pushout-product condition is exactly the
pullback-hom fibration condition; the unit axiom remains a separate conjunct. -/
theorem monoidalModelCategory_iff : MonoidalModelCategory C ↔
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C)) ∧ HasUnitAxiom C := by
  constructor
  · intro h
    exact ⟨(isQuillenBifunctor_iff_pullbackHom (MonoidalClosed.internalHomAdjunction₂ (C := C))).1
      h.pushoutProduct, h.unit⟩
  · rintro ⟨h, hu⟩
    exact ⟨(isQuillenBifunctor_iff_pullbackHom
      (MonoidalClosed.internalHomAdjunction₂ (C := C))).2 h,
      hu⟩

omit [MonoidalClosed C] in
/-- Canonical Mathlib pushout-products satisfy the cofibration condition. -/
lemma pushoutProduct_cofibration [IsQuillenBifunctor (curriedTensor C)]
    {A B X Y : C} (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j] :
    Cofibration (Arrow.mk i □ Arrow.mk j).hom :=
  IsQuillenBifunctor.cofibration i j (Functor.PushoutObjObj.ofHasPushout _ i j)
    inferInstance inferInstance

omit [MonoidalClosed C] in
lemma pushoutProduct_weakEquivalence [IsQuillenBifunctor (curriedTensor C)]
    {A B X Y : C} (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j]
    (h : WeakEquivalence i ∨ WeakEquivalence j) : WeakEquivalence (Arrow.mk i □ Arrow.mk j).hom :=
  IsQuillenBifunctor.weakEquivalence i j (Functor.PushoutObjObj.ofHasPushout _ i j)
    inferInstance inferInstance h

/-- The canonical closed pullback-hom is a fibration, and is trivial when
either input is trivial. -/
lemma pullbackHom_fibration [HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C))]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] :
    Fibration ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom :=
  HasQuillenPullbackHom.fibration i p (Functor.PullbackObjObj.ofHasPullback _ i p)
    inferInstance inferInstance

lemma pullbackHom_weakEquivalence [HasQuillenPullbackHom (MonoidalClosed.internalHom (C := C))]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p]
    (h : WeakEquivalence i ∨ WeakEquivalence p) :
    WeakEquivalence ((.op (Arrow.mk i)) ⋔ Arrow.mk p).hom :=
  HasQuillenPullbackHom.weakEquivalence i p (Functor.PullbackObjObj.ofHasPullback _ i p)
    inferInstance inferInstance h

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.8.12" (partial := component) "仮定：テンソルが Quillen 二関手で二本の射が余ファイブレーション（横射について HA と一致、比較四角形や対象の余ファイブラント性は要求しない）。結論：上段・下段に適用すると横の押し出し積が余ファイブレーションとなる部分に一致。縦射の弱同値性は型に含まれない。"] _root_.SerrePositivity.Quillen.pushoutProduct_cofibration
attribute [cite HA "4.5.4.10" (partial := special) "仮定：Quillen テンソルを持つモデル圏で底の二つの余ファイブレーションまたは余ファイブラント対象（Lean が強い：添字圏は両方とも一点、対象については組紐付き閉の場合）。結論：押し出し積が余ファイブレーション、テンソル積が余ファイブラント（その場合に二つの結論が一致）。一般の二つの射影図式の外部積は型に含まれない。"] _root_.SerrePositivity.Quillen.pushoutProduct_cofibration
attribute [cite HA "4.5.4.3" (partial := special) "仮定：モデル圏のテンソルが Quillen 二関手で、f が余ファイブレーション（HA の仮定の下で f を両入力とする）。結論：f□f が底で余ファイブレーション（n=2 で作用を忘れた主張に一致）。全ての n、自明性および Σₙ 射影余ファイブレーション性はこの型に含まれない。"] _root_.SerrePositivity.Quillen.pushoutProduct_cofibration
attribute [cite HTT "A.3.1.2" (partial := component) "仮定：閉モノイダル構造を外から与え、さらに原典どおり単位の cofibrancy を指定（HTT と一致）。結論：tensor の Quillen 条件と単位の identity replacement による弱い unit axiom を得る。native MonoidalModelCategory という一つの class は閉性も単位 cofibrancy も要求せず、原典の三条件をそのまま束ねた定義ではない。tensor の Quillen 条件の成分と、元の強い単位条件から弱い条件への方向を記録する。"] _root_.SerrePositivity.Quillen.MonoidalModelCategory
attribute [cite HTT "A.3.1.2" (partial := component) "仮定：閉モノイダル構造を外から与え、さらに原典どおり単位の cofibrancy を指定（HTT と一致）。結論：tensor の Quillen 条件と単位の identity replacement による弱い unit axiom を得る。native MonoidalModelCategory という一つの class は閉性も単位 cofibrancy も要求せず、原典の三条件をそのまま束ねた定義ではない。tensor の Quillen 条件の成分と、元の強い単位条件から弱い条件への方向を記録する。"] _root_.SerrePositivity.Quillen.unitAxiom_of_cofibrant_unit
attribute [cite HTT "A.3.1.3"] _root_.SerrePositivity.Quillen.HasUnitAxiom
attribute [cite HTT "A.3.1.3"] _root_.SerrePositivity.Quillen.UnitReplacementAxiom
