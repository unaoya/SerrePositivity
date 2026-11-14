module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Derived adjunctions for Quillen adjunctions

Absoluteness is proved using the cofibrant/fibrant derivability structures,
not assumed as an extra input. The adjunction, its unit/counit and comparison
maps are Mathlib's existing constructions. Arbitrary chosen derived functors
are accepted, so computation and uniqueness do not require a particular
replacement functor.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {HC : Type u₃} [Category.{v₃} HC] {HD : Type u₄} [Category.{v₄} HD]
  (QC : C ⥤ HC) [QC.IsLocalization (weakEquivalences C)]
  (QD : D ⥤ HD) [QD.IsLocalization (weakEquivalences D)]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [IsLeftQuillen L] [IsRightQuillen R]
  {LF : HC ⥤ HD} {RF : HD ⥤ HC}
  (α : QC ⋙ LF ⟶ L ⋙ QD) (β : R ⋙ QC ⟶ QD ⋙ RF)
  [LF.IsLeftDerivedFunctor α (weakEquivalences C)]
  [RF.IsRightDerivedFunctor β (weakEquivalences D)]

/-- The ordinary Quillen adjunction derives to an ordinary Mathlib adjunction. -/
noncomputable def derivedAdjunction : LF ⊣ RF := by
  have := leftDerived_postcomp QC QD α RF
  have := rightDerived_postcomp QC QD β LF
  exact adj.derived (weakEquivalences C) (weakEquivalences D) α β

/-- Computation of the derived unit against the left and right comparison maps. -/
@[reassoc]
lemma derivedAdjunction_unit_fac (X : C) :
    (derivedAdjunction QC QD adj α β).unit.app (QC.obj X) ≫ RF.map (α.app X) =
      QC.map (adj.unit.app X) ≫ β.app (L.obj X) := by
  have := leftDerived_postcomp QC QD α RF
  have := rightDerived_postcomp QC QD β LF
  exact adj.derivedη_fac_app (weakEquivalences C) α β X

/-- Computation of the derived counit against the comparison maps. -/
@[reassoc]
lemma derivedAdjunction_counit_fac (Y : D) :
    LF.map (β.app Y) ≫ (derivedAdjunction QC QD adj α β).counit.app (QD.obj Y) =
      α.app (R.obj Y) ≫ QD.map (adj.counit.app Y) := by
  have := leftDerived_postcomp QC QD α RF
  have := rightDerived_postcomp QC QD β LF
  exact adj.derivedε_fac_app (weakEquivalences D) α β Y

/-- The derived Hom equivalence computes the original mate on good objects;
this is also a compatibility law for the derived unit. -/
lemma derivedAdjunction_homEquiv (X : C) (Y : D) (f : L.obj X ⟶ Y) :
    (derivedAdjunction QC QD adj α β).homEquiv (QC.obj X) (QD.obj Y)
      (α.app X ≫ QD.map f) = QC.map (adj.homEquiv X Y f) ≫ β.app Y := by
  have hβ := β.naturality f
  dsimp at hβ
  rw [Adjunction.homEquiv_unit, RF.map_comp, ← Category.assoc,
    derivedAdjunction_unit_fac]
  rw [Category.assoc, ← hβ, ← Category.assoc,
    ← QC.map_comp, Adjunction.homEquiv_unit]

/-- The dual compatibility law computes the inverse mate. -/
lemma derivedAdjunction_homEquiv_symm (X : C) (Y : D) (g : X ⟶ R.obj Y) :
    ((derivedAdjunction QC QD adj α β).homEquiv (QC.obj X) (QD.obj Y)).symm
      (QC.map g ≫ β.app Y) = α.app X ≫ QD.map ((adj.homEquiv X Y).symm g) := by
  apply ((derivedAdjunction QC QD adj α β).homEquiv (QC.obj X) (QD.obj Y)).injective
  rw [Equiv.apply_symm_apply, derivedAdjunction_homEquiv, Equiv.apply_symm_apply]

section Uniqueness

variable {LF' : HC ⥤ HD} {RF' : HD ⥤ HC}
  (α' : QC ⋙ LF' ⟶ L ⋙ QD) (β' : R ⋙ QC ⟶ QD ⋙ RF')
  [LF'.IsLeftDerivedFunctor α' (weakEquivalences C)]
  [RF'.IsRightDerivedFunctor β' (weakEquivalences D)]

/-- Canonical comparison of any two choices of left derived functor. -/
noncomputable def leftChoiceIso : LF ≅ LF' :=
  Functor.leftDerivedUnique LF' LF α α' (weakEquivalences C)

/-- Canonical comparison of any two choices of right derived functor. -/
noncomputable def rightChoiceIso : RF ≅ RF' :=
  Functor.rightDerivedUnique RF RF' β β' (weakEquivalences D)

omit [ModelCategory D] [QD.IsLocalization (weakEquivalences D)] [IsLeftQuillen L] in
@[reassoc]
lemma leftChoiceIso_fac (X : C) :
    (leftChoiceIso (QC := QC) (QD := QD) α α').hom.app (QC.obj X) ≫ α'.app X = α.app X := by
  simp [leftChoiceIso, Functor.leftDerivedUnique, Functor.leftDerivedNatIso,
    Functor.leftDerivedNatTrans]

omit [ModelCategory C] [QC.IsLocalization (weakEquivalences C)] [IsRightQuillen R] in
@[reassoc]
lemma rightChoiceIso_fac (Y : D) :
    β.app Y ≫ (rightChoiceIso (QC := QC) (QD := QD) β β').hom.app (QD.obj Y) = β'.app Y := by
  simp [rightChoiceIso, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
    Functor.rightDerivedNatTrans]

/-- Changing both derived-functor choices transports the derived unit by the
canonical comparison isomorphisms. This is an equality of natural transformations. -/
lemma derivedAdjunction_unit_choice :
    (derivedAdjunction QC QD adj α β).unit ≫
      Functor.whiskerRight (leftChoiceIso (QC := QC) (QD := QD) α α').hom RF ≫
      Functor.whiskerLeft LF' (rightChoiceIso (QC := QC) (QD := QD) β β').hom =
        (derivedAdjunction QC QD adj α' β').unit := by
  have := leftDerived_postcomp QC QD α' RF'
  apply (LF' ⋙ RF').leftDerived_ext
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α' RF') (weakEquivalences C)
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  have heR := (rightChoiceIso (QC := QC) (QD := QD) β β').hom.naturality (α'.app X)
  dsimp at heR
  simp only [Category.assoc]
  rw [← heR, ← RF.map_comp_assoc, leftChoiceIso_fac,
    derivedAdjunction_unit_fac_assoc, rightChoiceIso_fac]
  exact (derivedAdjunction_unit_fac QC QD adj α' β' X).symm

/-- The derived counit is likewise independent of the chosen resolutions. -/
lemma derivedAdjunction_counit_choice :
    Functor.whiskerRight (rightChoiceIso (QC := QC) (QD := QD) β β').hom LF ≫
      Functor.whiskerLeft RF' (leftChoiceIso (QC := QC) (QD := QD) α α').hom ≫
      (derivedAdjunction QC QD adj α' β').counit =
        (derivedAdjunction QC QD adj α β).counit := by
  have := rightDerived_postcomp QC QD β LF
  apply (RF ⋙ LF).rightDerived_ext
    (Functor.whiskerRight β LF ≫ (Functor.associator _ _ _).hom) (weakEquivalences D)
  ext Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]
  have heL := (leftChoiceIso (QC := QC) (QD := QD) α α').hom.naturality (β'.app Y)
  dsimp at heL
  rw [← LF.map_comp_assoc, rightChoiceIso_fac]
  rw [← Category.assoc, heL, Category.assoc,
    derivedAdjunction_counit_fac, leftChoiceIso_fac_assoc]
  exact (derivedAdjunction_counit_fac QC QD adj α β Y).symm

end Uniqueness

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.5.1" (partial := direction) "仮定：抽象モデル圏 C,D の Quillen adjunction、元の weak-equivalence localizations と選んだ左右導来関手（HTT と一致）。結論：全 cofibrant X,fibrant Y の adjoint maps における weak equivalence の iff、すなわち条件 (3) から LF が equivalence、導来随伴により RF も equivalence となる方向は一致。導来同値から全 adjoint maps の判定へ戻す型はこの宣言にはなく、三条件全体の iff とは数えない。"] _root_.SerrePositivity.Quillen.derivedAdjunction
