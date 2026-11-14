module


public meta import SerrePositivity.Util.Citation
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Quillen conditions on ordinary functors and adjunctions

The model structures and adjunctions are Mathlib's existing types. The new classes
only assert preservation of the two relevant morphism classes. The adjunction
criterion is proved first for arbitrary weak factorization systems.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- An adjunction exchanges preservation of the left and right classes of weak
factorization systems. No model structure or functorial factorization is needed. -/
theorem preserves_left_iff_preserves_right {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (W₁ W₂ : MorphismProperty C) (V₁ V₂ : MorphismProperty D)
    [MorphismProperty.IsWeakFactorizationSystem W₁ W₂]
    [MorphismProperty.IsWeakFactorizationSystem V₁ V₂] :
    W₁ ≤ V₁.inverseImage L ↔ V₂ ≤ W₂.inverseImage R := by
  constructor
  · intro h X Y p hp
    change W₂ (R.map p)
    rw [← MorphismProperty.rlp_eq_of_wfs W₁ W₂]
    intro A B i hi
    exact (adj.hasLiftingProperty_iff i p).1
      (MorphismProperty.hasLiftingProperty_of_wfs (L.map i) p (h i hi) hp)
  · intro h A B i hi
    change V₁ (L.map i)
    rw [← MorphismProperty.llp_eq_of_wfs V₁ V₂]
    intro X Y p hp
    exact (adj.hasLiftingProperty_iff i p).2
      (MorphismProperty.hasLiftingProperty_of_wfs i (R.map p) hi (h p hp))

section Preservation

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [CategoryWithCofibrations D]
  [CategoryWithFibrations D] [CategoryWithWeakEquivalences D]
  [CategoryWithCofibrations E] [CategoryWithFibrations E]
  [CategoryWithWeakEquivalences E]

/-- Preservation of cofibrations and trivial cofibrations. Existence of a right
adjoint is supplied separately by an ordinary `Adjunction`. -/
class IsLeftQuillen (L : C ⥤ D) : Prop where
  map_cofibrations : cofibrations C ≤ (cofibrations D).inverseImage L
  map_trivialCofibrations : trivialCofibrations C ≤ (trivialCofibrations D).inverseImage L

/-- Preservation of fibrations and trivial fibrations. Existence of a left
adjoint is supplied separately by an ordinary `Adjunction`. -/
class IsRightQuillen (R : D ⥤ C) : Prop where
  map_fibrations : fibrations D ≤ (fibrations C).inverseImage R
  map_trivialFibrations : trivialFibrations D ≤ (trivialFibrations C).inverseImage R

instance isLeftQuillen_id : IsLeftQuillen (𝟭 C) where
  map_cofibrations := fun _ _ _ h ↦ h
  map_trivialCofibrations := fun _ _ _ h ↦ h

instance isRightQuillen_id : IsRightQuillen (𝟭 C) where
  map_fibrations := fun _ _ _ h ↦ h
  map_trivialFibrations := fun _ _ _ h ↦ h

instance isLeftQuillen_comp (L : C ⥤ D) (L' : D ⥤ E)
    [IsLeftQuillen L] [IsLeftQuillen L'] : IsLeftQuillen (L ⋙ L') where
  map_cofibrations := fun _ _ i hi ↦
    IsLeftQuillen.map_cofibrations (L := L') _ (IsLeftQuillen.map_cofibrations (L := L) i hi)
  map_trivialCofibrations := fun _ _ i hi ↦
    IsLeftQuillen.map_trivialCofibrations (L := L') _
      (IsLeftQuillen.map_trivialCofibrations (L := L) i hi)

instance isRightQuillen_comp (R : D ⥤ C) (R' : E ⥤ D)
    [IsRightQuillen R] [IsRightQuillen R'] : IsRightQuillen (R' ⋙ R) where
  map_fibrations := fun _ _ p hp ↦
    IsRightQuillen.map_fibrations (R := R) _ (IsRightQuillen.map_fibrations (R := R') p hp)
  map_trivialFibrations := fun _ _ p hp ↦
    IsRightQuillen.map_trivialFibrations (R := R) _
      (IsRightQuillen.map_trivialFibrations (R := R') p hp)

omit [CategoryWithFibrations C] [CategoryWithFibrations D] in
lemma map_cofibration (L : C ⥤ D) [IsLeftQuillen L] {X Y : C} (i : X ⟶ Y)
    [Cofibration i] : Cofibration (L.map i) :=
  (cofibration_iff _).2 (IsLeftQuillen.map_cofibrations i (mem_cofibrations i))

omit [CategoryWithFibrations C] [CategoryWithFibrations D] in
lemma map_weakEquivalence_of_cofibration (L : C ⥤ D) [IsLeftQuillen L]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence (L.map i) :=
  (weakEquivalence_iff _).2
    (IsLeftQuillen.map_trivialCofibrations i (mem_trivialCofibrations i)).2

omit [CategoryWithCofibrations C] [CategoryWithCofibrations D] in
lemma map_fibration (R : D ⥤ C) [IsRightQuillen R] {X Y : D} (p : X ⟶ Y)
    [Fibration p] : Fibration (R.map p) :=
  (fibration_iff _).2 (IsRightQuillen.map_fibrations p (mem_fibrations p))

omit [CategoryWithCofibrations C] [CategoryWithCofibrations D] in
lemma map_weakEquivalence_of_fibration (R : D ⥤ C) [IsRightQuillen R]
    {X Y : D} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] :
    WeakEquivalence (R.map p) :=
  (weakEquivalence_iff _).2
    (IsRightQuillen.map_trivialFibrations p (mem_trivialFibrations p)).2

end Preservation

section Model

variable [ModelCategory C] [ModelCategory D]

/-- For an ordinary adjunction between model categories, the two Quillen
preservation conditions are equivalent. -/
theorem isLeftQuillen_iff_isRightQuillen {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    IsLeftQuillen L ↔ IsRightQuillen R := by
  constructor
  · intro h
    exact ⟨(preserves_left_iff_preserves_right adj
      (trivialCofibrations C) (fibrations C) (trivialCofibrations D) (fibrations D)).1
        h.map_trivialCofibrations,
      (preserves_left_iff_preserves_right adj
        (cofibrations C) (trivialFibrations C) (cofibrations D) (trivialFibrations D)).1
        h.map_cofibrations⟩
  · intro h
    exact ⟨(preserves_left_iff_preserves_right adj
      (cofibrations C) (trivialFibrations C) (cofibrations D) (trivialFibrations D)).2
        h.map_trivialFibrations,
      (preserves_left_iff_preserves_right adj
        (trivialCofibrations C) (fibrations C) (trivialCofibrations D) (fibrations D)).2
        h.map_fibrations⟩

lemma isRightQuillen_of_isLeftQuillen {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [IsLeftQuillen L] : IsRightQuillen R :=
  (isLeftQuillen_iff_isRightQuillen adj).1 inferInstance

lemma isLeftQuillen_of_isRightQuillen {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [IsRightQuillen R] : IsLeftQuillen L :=
  (isLeftQuillen_iff_isRightQuillen adj).2 inferInstance

end Model

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.3.7.2" (partial := direction) "仮定：抽象モデル圏の実際の随伴 L⊣R と left Quillen L（元の (1)、simplicial 条件を不要にする弱い仮定）。結論：L の cofibration 保存と R の fibrant object 保存を得るので (1)⇒(2) に一致。逆向きは native isLeftQuillen_of_fibrant_test が fibrant 対象間の fibration 保存も要求し、fibrant objects 保存のみからは証明していない。"] _root_.SerrePositivity.Quillen.IsLeftQuillen.map_cofibrations
attribute [cite HTT "A.3.7.2" (partial := direction) "仮定：抽象モデル圏の実際の随伴 L⊣R と left Quillen L（元の (1)、simplicial 条件を不要にする弱い仮定）。結論：L の cofibration 保存と R の fibrant object 保存を得るので (1)⇒(2) に一致。逆向きは native isLeftQuillen_of_fibrant_test が fibrant 対象間の fibration 保存も要求し、fibrant objects 保存のみからは証明していない。"] _root_.SerrePositivity.Quillen.isRightQuillen_of_isLeftQuillen
