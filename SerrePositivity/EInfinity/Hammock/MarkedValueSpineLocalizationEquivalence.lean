module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineLocalizationMarked

/-!
# 元の通常の局所化と指定値の因子列の圏の同値

概要：局所化比較の両方の合成が元の恒等関手へ厳密に一致する。
方針：指定値上の往復と非指定生成矢上の往復を元の全列で合成する。
規約：元の Q と元の全値の因子列を保持する。
使われ方：元の通常の局所化 Hom の具体的な回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

lemma ValueSpine.cons_decomposition {X Y : Paths C} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
    (p : valueHomType W X g.val.left) (t : ValueSpine W Y g.val.right) :
    ValueSpine.compose (ValueSpine.nil X p) (ValueSpine.compose (ValueSpine.generator W g) t) =
      ValueSpine.cons X g p t := by
  cases t <;> simp only [ValueSpine.generator, ValueSpine.compose, ValueSpine.precompose,
    Category.comp_id, Category.id_comp]

lemma valueToLocalization_localizationToValue_map {X Y : Paths C} (t : ValueSpine W Y X) :
    letI := valueCategory W
    (localizationToValue W).map ((valueToLocalization W).map t) = t := by
  let := valueCategory W
  induction t with
  | nil X p => exact localizationToValue_marked W p
  | cons X g p t ih =>
    change (localizationToValue W).map
      ((markedValueDescent W W.paths.Q W.paths.Q_inverts).map p ≫
        W.paths.Q.map g.val.hom.toPath ≫ (valueToLocalization W).map t) = _
    rw [Functor.map_comp, Functor.map_comp, localizationToValue_marked,
      localizationToValue_unmarked, ih]
    exact ValueSpine.cons_decomposition W g p t

lemma valueToLocalization_localizationToValue : letI := valueCategory W
    valueToLocalization W ⋙ localizationToValue W = 𝟭 (ValueObjects C) := by
  let := valueCategory W
  refine CategoryTheory.Functor.ext (F := valueToLocalization W ⋙ localizationToValue W)
    (G := 𝟭 (ValueObjects C)) (fun _ => rfl) ?_
  intro X Y t
  simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact valueToLocalization_localizationToValue_map W t

def valueLocalizationEquivalence : letI := valueCategory W
    W.paths.Localization ≌ ValueObjects C := by
  letI := valueCategory W
  exact CategoryTheory.Equivalence.mk (localizationToValue W) (valueToLocalization W)
    (eqToIso (localizationToValue_valueToLocalization W).symm)
    (eqToIso (valueToLocalization_localizationToValue W))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
