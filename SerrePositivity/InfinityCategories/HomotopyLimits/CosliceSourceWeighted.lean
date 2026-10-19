module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceSourcePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeInitialWeighted
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCoslicePrecomposition

/-!
概要：coslice 全体の前合成を、既存の weighted な比較と厳密に照合する。
方針：weighted coslice の単体を固定初点の座標へ戻し、coherent simplex 全体の等式を使う。
規約：全 Hom パラメータの射として一致する。極限性の仮定は使わない。
使われ方：HTT 4.2.4.1 の錐全体上の族から元の図式への制限の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- weighted coslice の固定初点座標は、元の weighted cone simplex を回収する。 -/
lemma cosliceInitialCoordinates_weighted (F : I ⥤ C) (z : C) {n : ℕ}
    (s : (weightedNerve (simplicialHomDiagram F z ⋙ SSet.opFunctor)) _⦋n⦌) :
    cosliceInitialCoordinates z (weightedCosliceSimplex F z s) =
      (⟨weightedConeSimplex F z s.2, rfl⟩ : fixedInitialSimplex z n) := by
  apply Subtype.ext
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (weightedConeSimplex F z s.2))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- coslice 全体の前合成は、weighted な係数から構成した既存の族を厳密に回収する。 -/
lemma coherentCosliceSourcePrecomposition_weighted (F : I ⥤ C) (x z : C) :
    (weightedCosliceComparison F z ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
      coherentCosliceSourcePrecomposition x z = weightedCoslicePrecompositionFamily F x z := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  apply Subtype.ext
  change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (coneInitialFixedSimplex x
        (cosliceInitialCoordinates z (weightedCosliceSimplex F z s.down))
        (SSet.yonedaEquiv.symm a.down)) =
    (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (weightedConeSimplex F x
        ((weightedConePrecompositionMap F x z).app (Opposite.op ⦋n⦌) (s.down, a.down)).2)
  rw [cosliceInitialCoordinates_weighted]
  change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (coneInitialSimplex x (weightedConeSimplex F z s.down.2)
        (SSet.yonedaEquiv.symm a.down)) = _
  rw [coneInitialSimplex_weighted]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
