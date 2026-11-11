module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineLocalization

/-!
# 元の指定自由 groupoid 上の局所化比較の往復

概要：元の指定生成矢・逆射・全合成について局所化比較の往復が元の包含に一致する。
方針：自由 groupoid の元の射の帰納法と元の二つの回収式を使う。
規約：元の指定値の包含を保持し、射の正規形を仮定しない。
使われ方：値の因子列の全 Hom での比較の往復。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

lemma localizationToValue_Qmap {X Y : Paths C} (p : X ⟶ Y) : letI := valueCategory W
    (localizationToValue W).map (W.paths.Q.map p) = (valueLift W).map p := by
  let := valueCategory W
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    using CategoryTheory.Functor.congr_hom (localizationToValue_fac W) p

lemma localizationToValue_marked_generator {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W} (f : X ⟶ Y) :
    letI := valueCategory W
    (localizationToValue W).map ((markedValueDescent W W.paths.Q W.paths.Q_inverts).map
      ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f)) =
      (valueMarkedFunctor W).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f) := by
  let := valueCategory W
  rw [markedValueDescent_generator, localizationToValue_Qmap]
  exact valueLift_marked W f.val f.property

lemma localizationToValue_marked {X Y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)}
    (p : X ⟶ Y) : letI := valueCategory W
    (localizationToValue W).map ((markedValueDescent W W.paths.Q W.paths.Q_inverts).map p) =
      (valueMarkedFunctor W).map p := by
  let := valueCategory W
  let K := markedValueDescent W W.paths.Q W.paths.Q_inverts
  let T := localizationToValue W
  let J := valueMarkedFunctor W
  change T.map (K.map p) = J.map p
  refine Quiver.FreeGroupoid.hom_rec (motive := fun {_ _} p => T.map (K.map p) = J.map p)
    ?_ ?_ ?_ ?_ p
  · intro X Y f
    exact localizationToValue_marked_generator W f
  · intro X Y f
    rw [K.map_inv, T.map_inv, J.map_inv]
    have hi : asIso (T.map (K.map
        ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f))) =
        asIso (J.map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W)).map f)) :=
      Iso.ext (localizationToValue_marked_generator W f)
    exact congrArg Iso.inv hi
  · intro X
    rw [K.map_id, T.map_id, J.map_id]
    rfl
  · intro X Y Z f g hf hg
    rw [K.map_comp, T.map_comp, J.map_comp, hf, hg]

lemma localizationToValue_unmarked (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : letI := valueCategory W
    (localizationToValue W).map (W.paths.Q.map g.val.hom.toPath) = ValueSpine.generator W g := by
  let := valueCategory W
  rw [localizationToValue_Qmap]
  exact valueLift_unmarked W g.val.hom g.property

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
