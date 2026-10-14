module

public import SerrePositivity.CategoryTheory.Monoidal.MappingAssociativity
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # 通常の射から写像対象の点への対応と合成 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingArrowComposition

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 二つの通常の射の点を合成した後の評価の法則。 -/
def arrowCompositionEvaluationLaw {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (H.map (p ⊗ₘ q)).app E ≫ MappingAssociativity.compositionEvaluation H a P Q v w =
    (H.map (λ_ (𝟙_ V)).hom).app E ≫ u.hom.app E ≫ f ≫ g

/-- 結同比較の自然性と作用の単位により、点の合成の評価は元の射の合成になる。 -/
lemma arrow_composition_evaluation {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hv : (H.map q).app E ≫ v = u.hom.app E ≫ f)
    (hw : (H.map p).app F ≫ w = u.hom.app F ≫ g)
    (ha : (H.map (p ⊗ₘ q)).app E ≫ (a P Q).hom.app E =
      (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.map p).app ((H.obj (𝟙_ V)).obj E) ≫
        (H.obj P).map ((H.map q).app E))
    (hu : (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) =
      (H.map (ρ_ (𝟙_ V)).hom).app E) :
    arrowCompositionEvaluationLaw H a u f g p q v w := by
  unfold arrowCompositionEvaluationLaw MappingAssociativity.compositionEvaluation
  rw [reassoc_of% ha, ← CategoryTheory.Functor.map_comp_assoc, hv]
  rw [← reassoc_of% ((H.map p).naturality (u.hom.app E ≫ f))]
  rw [hw]
  rw [(H.obj (𝟙_ V)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (u.hom.naturality f)]
  change (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) ≫
    u.hom.app E ≫ f ≫ g = _
  rw [reassoc_of% hu, ← unitors_equal]

/-- 表現性を使った通常の射と写像対象の点の合成の一致の等式。 -/
def representedArrowCompositionLaw {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫
    adj.homEquiv _ G (MappingAssociativity.compositionEvaluation H a P Q v w) =
      AdjunctionHomLaws.comparisonHomEquiv adj (u.app E) G (f ≫ g)

/-- 点の合成の評価を表現性で戻すと、元の射の合成に対応する。 -/
lemma represented_arrow_composition {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (h : arrowCompositionEvaluationLaw H a u f g p q v w) :
    representedArrowCompositionLaw H a u adj f g p q v w := by
  unfold representedArrowCompositionLaw
  rw [AdjunctionHomLaws.comparisonHomEquiv_apply]
  apply (cancel_epi (λ_ (𝟙_ V)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply AdjunctionHomLaws.curry_pre_comparison_of_evaluation adj
  exact h

end SerrePositivity.MappingArrowComposition
