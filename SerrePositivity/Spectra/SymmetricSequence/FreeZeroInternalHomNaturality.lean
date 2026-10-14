module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolution
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomNaturality

/-! # 生成次数零の内部Homの比較と通常の前合成・後合成 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 各段の通常の内部Homの前合成と後合成から得る対称列の射。 -/
def unshiftedInternalHomMap {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    unshiftedInternalHom Y F ⟶ unshiftedInternalHom X G :=
  CategoryTheory.Functor.whiskerLeft (toFunctorCategory.obj F) (pre f) ≫
    CategoryTheory.Functor.whiskerRight (toFunctorCategory.map g) (ihom X)

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- 通常の内部Homの射の各段は、前合成してから後合成する射。 -/
lemma unshiftedInternalHomMap_app {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) (q : ℕ) :
    (unshiftedInternalHomMap f g).app (FiniteBijection.of q) =
      (pre f).app (level F q) ≫ (ihom X).map (g.app (FiniteBijection.of q)) := rfl

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] in
/-- 零生成次数のずれを除く比較は両変数の射に関して自然。 -/
@[reassoc]
lemma zeroShiftInternalHomIso_naturality {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    shiftedInternalHomMap 0 f g ≫ (zeroShiftInternalHomIso X G).hom =
      (zeroShiftInternalHomIso Y F).hom ≫ unshiftedInternalHomMap f g := by
  apply NatTrans.ext
  funext a
  change ((pre f).app (F.obj ((𝟙_ FiniteBijection) ⊗ a)) ≫
      (ihom X).map (g.app ((𝟙_ FiniteBijection) ⊗ a))) ≫
        (ihom X).map (G.map (λ_ a).hom) =
    (ihom Y).map (F.map (λ_ a).hom) ≫
      ((pre f).app (F.obj a) ≫ (ihom X).map (g.app a))
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp, ← g.naturality,
    CategoryTheory.Functor.map_comp]
  erw [← Category.assoc, ← (pre f).naturality, Category.assoc]

/-- 自由零生成対称列からの内部Homの比較は両変数の射に関して自然。 -/
@[reassoc]
lemma freeZeroInternalHomNatIso_naturality {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    (pre ((freeAt 0).map f)).app F ≫ (ihom ((freeAt 0).obj X)).map g ≫
        (freeZeroInternalHomNatIso X).hom.app G =
      (freeZeroInternalHomNatIso Y).hom.app F ≫ unshiftedInternalHomMap f g := by
  change (pre ((freeAt 0).map f)).app F ≫ (ihom ((freeAt 0).obj X)).map g ≫
      ((freeInternalHomSequenceIso 0 X G).hom ≫ (zeroShiftInternalHomIso X G).hom) =
    ((freeInternalHomSequenceIso 0 Y F).hom ≫ (zeroShiftInternalHomIso Y F).hom) ≫ _
  simp only [Category.assoc]
  rw [freeInternalHomSequenceIso_naturality_assoc, zeroShiftInternalHomIso_naturality]

/-- 比較の順逆で自由零生成対称列からの射を移すと通常の前合成・後合成になる。 -/
lemma freeZeroInternalHomNatIso_conjugate {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G) :
    (freeZeroInternalHomNatIso Y).inv.app F ≫ (pre ((freeAt 0).map f)).app F ≫
        (ihom ((freeAt 0).obj X)).map g ≫ (freeZeroInternalHomNatIso X).hom.app G =
      unshiftedInternalHomMap f g := by
  rw [freeZeroInternalHomNatIso_naturality]
  erw [Iso.inv_hom_id_assoc]

end SerrePositivity.SymmetricSequence
