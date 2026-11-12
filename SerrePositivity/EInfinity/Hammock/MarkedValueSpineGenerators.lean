module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineCategory

/-!
# 元の自由圏から指定値の因子列の圏への関手

概要：元の指定生成矢を長さ零の指定値、非指定生成矢を一段の列へ送る。
方針：元の各生成矢で場合分けし、Paths.lift で全射列へ延長する。
規約：元の恒等射を表す生成矢も削除しない。
使われ方：値の因子列の圏を通常の局所化として同定する。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def ValueSpine.generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : ValueSpine W g.val.right g.val.left :=
  .cons g.val.left g (𝟙 _) (.nil g.val.right (𝟙 _))

def valuePrefunctor : letI := valueCategory W
    C ⥤q ValueObjects C := by
  letI := valueCategory W
  exact
    { obj X := X
      map {X Y} f := by
        classical
        exact if hf : W f then ValueSpine.nil X
          ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map ⟨f, hf⟩)
          else ValueSpine.generator W ⟨⟨X, Y, f⟩, hf⟩ }

def valueLift : letI := valueCategory W
    Paths C ⥤ ValueObjects C := by
  letI := valueCategory W
  exact Paths.lift (valuePrefunctor W)

lemma valueLift_marked {X Y : C} (f : X ⟶ Y) (hf : W f) : letI := valueCategory W
    (valueLift W).map f.toPath = (valueMarkedFunctor W).map
      ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map ⟨f, hf⟩) := by
  classical
  let := valueCategory W
  simp only [valueLift, Paths.lift_toPath, valuePrefunctor, dite_eq_left hf]
  rfl

lemma valueLift_unmarked {X Y : C} (f : X ⟶ Y) (hf : ¬ W f) : letI := valueCategory W
    (valueLift W).map f.toPath = ValueSpine.generator W ⟨⟨X, Y, f⟩, hf⟩ := by
  classical
  let := valueCategory W
  simp only [valueLift, Paths.lift_toPath, valuePrefunctor, dite_eq_right hf]

lemma valueLift_marked_fac : letI := valueCategory W
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ valueLift W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation (Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⋙
        valueMarkedFunctor W := by
  let := valueCategory W
  apply Paths.ext_functor (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ valueLift W)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation (Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⋙
      valueMarkedFunctor W) (funext (fun _ => rfl))
  intro X Y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (valueLift W).map f.val.toPath = _
  exact valueLift_marked W f.val f.property

lemma valueLift_inverts : letI := valueCategory W
    W.paths.IsInvertedBy (valueLift W) := by
  let := valueCategory W
  intro X Y p hp
  obtain ⟨q, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_range W p).mpr hp
  have he : (valueLift W).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map q) =
      (valueMarkedFunctor W).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map q) :=
    by simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
      using CategoryTheory.Functor.congr_hom (valueLift_marked_fac W) q
  rw [he]
  infer_instance

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
