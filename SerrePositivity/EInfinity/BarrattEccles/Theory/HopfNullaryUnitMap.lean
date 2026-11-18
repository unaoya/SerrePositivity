module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorUnitObject
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryFamilyAdjacent

/-!
# 指定単位射と零入力の作用

HA 3.2.4.7 の自由比較で、単位代数からの指定射を零入力係数で計算する。
始対象性で選ばれた射も、実際の代数の零入力作用で固定される。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 単位代数からの任意の代数射は、零入力の作用と可換である。 -/
lemma hopfTensorUnitArrow_nullary (hP : P.Hopf) (Y : P.Algebra)
    (f : hopfTensorUnitObject hP ⟶ Y) :
    hP.counit.map.app (FiniteBijection.of 0) ≫ f.hom =
      (ρ_ (P.arity 0)).inv ≫ Y.action 0 := by
  have h := f.comm 0
  change ((hP.counit.map.app (FiniteBijection.of 0) ▷ 𝟙_ (Complex A)) ≫
    (λ_ (𝟙_ (Complex A))).hom ≫ 𝟙 _) ≫ f.hom =
      (𝟙 (P.arity 0) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ Y.action 0 at h
  have h' := congrArg (fun g => (ρ_ (P.arity 0)).inv ≫ g) h
  simp only [Category.assoc, Category.comp_id, tensorHom_id, id_whiskerRight,
    Category.id_comp] at h'
  rw [← rightUnitor_inv_naturality_assoc] at h'
  change hP.counit.map.app (FiniteBijection.of 0) ≫
    (ρ_ (𝟙_ (Complex A))).inv ≫ (λ_ (𝟙_ (Complex A))).hom ≫ f.hom = _ at h'
  have hu : (ρ_ (𝟙_ (Complex A))).inv ≫ (λ_ (𝟙_ (Complex A))).hom = 𝟙 _ := by
    monoidal
  simpa only [reassoc_of% hu, Category.id_comp] using h'

/-- 指定単位射は、零入力の余単位の逆と実際の零入力作用の合成である。 -/
lemma hopfTensorUnitMap_hom_nullary (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (Y : P.Algebra) :
    (hopfTensorUnitMap hP h0 Y).hom =
      inv (hP.counit.map.app (FiniteBijection.of 0)) ≫
        (ρ_ (P.arity 0)).inv ≫ Y.action 0 := by
  have := h0
  apply (cancel_epi (hP.counit.map.app (FiniteBijection.of 0))).1
  rw [IsIso.hom_inv_id_assoc]
  exact hopfTensorUnitArrow_nullary hP Y _

namespace BarrattEccles
variable (R : Type u) [CommRing R]

/-- BE の零入力係数の指定同型は、同じ Hopf 余単位である。 -/
lemma hopf_counit_zero_eq_nullaryCoefficientIso :
    (hopf R).counit.map.app (FiniteBijection.of 0) = (nullaryCoefficientIso R).hom := by
  change (augmentation R).map.app (FiniteBijection.of 0) = _
  rw [augmentation_app]
  rfl

/-- 始対象性から選んだ BE の単位射を、指定零入力係数の逆で計算する。 -/
lemma barrattEcclesTensorUnitMap_nullary
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0)))
    (Y : (operad R).Algebra) :
    (hopfTensorUnitMap (hopf R) h0 Y).hom =
      (nullaryCoefficientIso R).inv ≫ (ρ_ ((operad R).arity 0)).inv ≫ Y.action 0 := by
  have := h0
  have hi : inv ((hopf R).counit.map.app (FiniteBijection.of 0)) =
      (nullaryCoefficientIso R).inv := by
    apply (cancel_epi ((hopf R).counit.map.app (FiniteBijection.of 0))).1
    rw [IsIso.hom_inv_id]
    erw [hopf_counit_zero_eq_nullaryCoefficientIso]
    exact (nullaryCoefficientIso R).hom_inv_id.symm
  rw [hopfTensorUnitMap_hom_nullary, hi]

end BarrattEccles
end SerrePositivity.EInfinity
