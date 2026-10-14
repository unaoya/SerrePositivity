module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomSequenceIso
public import SerrePositivity.Spectra.SymmetricSequence.ConvolutionMiddleExchangeUnit

/-! # 各段の通常の内部Homと生成次数零の対称列全体の比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 各段でXからの通常の内部Homを取った対称列。 -/
def unshiftedInternalHom (X : C) (F : SymmetricSequence C) : SymmetricSequence C :=
  toFunctorCategory.obj F ⋙ ihom X

/-- 各段の通常の内部Homには次数のずれがない。 -/
lemma unshiftedInternalHom_level (X : C) (F : SymmetricSequence C) (q : ℕ) :
    level (unshiftedInternalHom X F) q = (ihom X).obj (level F q) := by
  rfl

/-- 生成次数零のずれを左単位子で除く、対称列全体の比較。 -/
def zeroShiftInternalHomIso (X : C) (F : SymmetricSequence C) :
    shiftedInternalHom 0 X F ≅ unshiftedInternalHom X F :=
  NatIso.ofComponents (fun a =>
    (toFunctorCategory.obj F ⋙ ihom X).mapIso (λ_ a)) (by
      intro a b f
      change (toFunctorCategory.obj F ⋙ ihom X).map ((𝟙_ FiniteBijection) ◁ f) ≫
          (toFunctorCategory.obj F ⋙ ihom X).map (λ_ b).hom =
        (toFunctorCategory.obj F ⋙ ihom X).map (λ_ a).hom ≫
          (toFunctorCategory.obj F ⋙ ihom X).map f
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        leftUnitor_naturality])

/-- 第q段の順比較は、零加法による値域の移送の後合成。 -/
lemma zeroShiftInternalHomIso_hom_app (X : C) (F : SymmetricSequence C) (q : ℕ) :
    (zeroShiftInternalHomIso X F).hom.app (FiniteBijection.of q) =
      (ihom X).map (eqToHom (congrArg (level F) (Nat.zero_add q))) := by
  change (ihom X).map (F.map (λ_ (FiniteBijection.of q)).hom) = _
  rw [FiniteBijection.leftUnitor_of_hom]
  erw [eqToHom_map]

/-- 第q段の逆比較は、零加法による逆の値域移送の後合成。 -/
lemma zeroShiftInternalHomIso_inv_app (X : C) (F : SymmetricSequence C) (q : ℕ) :
    (zeroShiftInternalHomIso X F).inv.app (FiniteBijection.of q) =
      (ihom X).map (eqToHom (congrArg (level F) (Nat.zero_add q).symm)) := by
  change (ihom X).map (F.map (λ_ (FiniteBijection.of q)).inv) = _
  rw [FiniteBijection.leftUnitor_of_inv]
  erw [eqToHom_map]

end SerrePositivity.SymmetricSequence
