module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineFold
public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineCoreDescent

/-!
# 元の反転関手の指定値の因子列からの延長

概要：元の指定矢を反転する関手を、同じ値の因子列の圏から延長する。
方針：指定部分の Core への自由延長と非指定生成矢の元の像を列で合成する。
規約：元の自由圏からの関手を厳密に回収する。
使われ方：通常の局所化 Hom との比較。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [Category.{vD} D] (F : Paths C ⥤ D) (hF : W.paths.IsInvertedBy F)

def valueDescent : letI := valueCategory W
    ValueObjects C ⥤ D := by
  letI := valueCategory W
  exact valueFoldFunctor W (markedValueDescent W F hF) (fun g => F.map g.val.hom.toPath)

lemma valueDescent_marked : letI := valueCategory W
    valueMarkedFunctor W ⋙ valueDescent W F hF = markedValueDescent W F hF :=
  valueFoldFunctor_marked W _ _

lemma valueDescent_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) : letI := valueCategory W
    (valueDescent W F hF).map (ValueSpine.generator W g) = F.map g.val.hom.toPath :=
  valueFoldFunctor_generator W _ _ g

lemma valueDescent_fac : letI := valueCategory W
    valueLift W ⋙ valueDescent W F hF = F := by
  let := valueCategory W
  apply Paths.ext_functor (F := valueLift W ⋙ valueDescent W F hF) (G := F)
    (funext (fun _ => rfl))
  intro X Y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  by_cases hf : W f
  · rw [valueLift_marked W f hf]
    exact markedValueDescent_generator W F hF ⟨f, hf⟩
  · rw [valueLift_unmarked W f hf]
    exact valueDescent_generator W F hF ⟨⟨X, Y, f⟩, hf⟩

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
