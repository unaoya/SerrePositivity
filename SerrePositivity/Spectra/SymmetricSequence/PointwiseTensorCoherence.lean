module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule

/-! # 各段のテンソルの比較の公式から得る作用の整合性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]
  (a : ∀ X Y : C, ∀ A : Mod (SymmetricSequence C) M,
    pointwiseTensorModule M (X ⊗ Y) A ≅
      pointwiseTensorModule M X (pointwiseTensorModule M Y A))
  (e : ∀ A : Mod (SymmetricSequence C) M, pointwiseTensorModule M (𝟙_ C) A ≅ A)
  (p : ∀ {X Y : C}, (X ⟶ Y) → ∀ A : Mod (SymmetricSequence C) M,
    pointwiseTensorModule M X A ⟶ pointwiseTensorModule M Y A)

/-- 作用の五角形の等式。 -/
def pointwiseActionPentagonLaw (X Y Z : C) (A : Mod (SymmetricSequence C) M) : Prop :=
  p (α_ X Y Z).hom A ≫ (a X (Y ⊗ Z) A).hom ≫
    (pointwiseTensorModuleFunctor M X).map (a Y Z A).hom =
  (a (X ⊗ Y) Z A).hom ≫ (a X Y (pointwiseTensorModule M Z A)).hom

/-- 作用の右単位の三角形の等式。 -/
def pointwiseActionTriangleLaw (X : C) (A : Mod (SymmetricSequence C) M) : Prop :=
  (a X (𝟙_ C) A).hom ≫ (pointwiseTensorModuleFunctor M X).map (e A).hom =
    p (ρ_ X).hom A

/-- 作用の左単位の整合性の等式。 -/
def pointwiseActionLeftUnitLaw (X : C) (A : Mod (SymmetricSequence C) M) : Prop :=
  (a (𝟙_ C) X A).hom ≫ (e (pointwiseTensorModule M X A)).hom = p (λ_ X).hom A

variable
  (ha : ∀ X Y A q, (a X Y A).hom.hom.app (FiniteBijection.of q) =
    (α_ X Y (level A.X q)).hom)
  (he : ∀ A q, (e A).hom.hom.app (FiniteBijection.of q) = (λ_ (level A.X q)).hom)
  (hp : ∀ {X Y} (f : X ⟶ Y) A q,
    (p f A).hom.app (FiniteBijection.of q) = f ▷ level A.X q)

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
include ha hp in
/-- 各段の結合子と生成対象の射の公式から作用の五角形を得る。 -/
lemma pointwiseAction_pentagon (X Y Z : C) (A : Mod (SymmetricSequence C) M) :
    pointwiseActionPentagonLaw M a p X Y Z A := by
  unfold pointwiseActionPentagonLaw
  apply Mod.hom_ext
  apply hom_ext
  intro q
  change (p (α_ X Y Z).hom A).hom.app (FiniteBijection.of q) ≫
    (a X (Y ⊗ Z) A).hom.hom.app (FiniteBijection.of q) ≫
      ((pointwiseTensorModuleFunctor M X).map (a Y Z A).hom).hom.app
        (FiniteBijection.of q) =
    (a (X ⊗ Y) Z A).hom.hom.app (FiniteBijection.of q) ≫
      (a X Y (pointwiseTensorModule M Z A)).hom.hom.app (FiniteBijection.of q)
  rw [hp, pointwiseTensorModuleFunctor_map_app, ha, ha, ha, ha]
  exact CategoryTheory.MonoidalCategory.pentagon X Y Z (level A.X q)

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
include ha he hp in
/-- 各段の単位子と結合子の公式から作用の三角形を得る。 -/
lemma pointwiseAction_triangle (X : C) (A : Mod (SymmetricSequence C) M) :
    pointwiseActionTriangleLaw M a e p X A := by
  unfold pointwiseActionTriangleLaw
  apply Mod.hom_ext
  apply hom_ext
  intro q
  change (a X (𝟙_ C) A).hom.hom.app (FiniteBijection.of q) ≫
    ((pointwiseTensorModuleFunctor M X).map (e A).hom).hom.app (FiniteBijection.of q) =
    (p (ρ_ X).hom A).hom.app (FiniteBijection.of q)
  rw [ha, pointwiseTensorModuleFunctor_map_app, he, hp]
  exact CategoryTheory.MonoidalCategory.triangle X (level A.X q)

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
include ha he hp in
/-- 各段の左単位子と結合子の公式から作用の左単位の整合性を得る。 -/
lemma pointwiseAction_left_unit (X : C) (A : Mod (SymmetricSequence C) M) :
    pointwiseActionLeftUnitLaw M a e p X A := by
  unfold pointwiseActionLeftUnitLaw
  apply Mod.hom_ext
  apply hom_ext
  intro q
  change (a (𝟙_ C) X A).hom.hom.app (FiniteBijection.of q) ≫
    (e (pointwiseTensorModule M X A)).hom.hom.app (FiniteBijection.of q) =
    (p (λ_ X).hom A).hom.app (FiniteBijection.of q)
  rw [ha, he, hp]
  exact (CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight X (level A.X q)).symm

end SerrePositivity.SymmetricSequence
