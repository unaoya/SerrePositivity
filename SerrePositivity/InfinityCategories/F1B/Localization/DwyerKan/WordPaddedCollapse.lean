module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordForwardFixed
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPadding
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordUnit
public import Mathlib.Tactic.FinCases

/-!
# 元の両端 padding と三列の語の回収

概要：一列 forward に両端 backward を付けた語を元の threeArrow と同定する。
方針：元の三列の向きを照合し、中央の合成を同じ語の射へ束ねる。
規約：同型類ではなく元の語の等式と元の射の自然性を提供する。
使われ方：forward 部分語図式の余極限から元の三本矢の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma padding_single_forward : paddingFunctor.obj (single .forward) = threeArrow := by
  apply object_ext (paddingFunctor.obj (single .forward)) threeArrow rfl
  intro i
  change Fin 3 at i
  fin_cases i <;> rfl

def paddedCollapse (a : Word) : paddingFunctor.obj (forwardCore a) ⟶ threeArrow :=
  paddingFunctor.map (forwardCollapse a) ≫ eqToHom padding_single_forward

lemma paddedCollapse_naturality {a b : Word} (f : a ⟶ b) :
    paddingFunctor.map (forwardMap f) ≫ paddedCollapse b = paddedCollapse a := by
  change paddingFunctor.map (forwardMap f) ≫
    (paddingFunctor.map (forwardCollapse b) ≫ eqToHom padding_single_forward) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, forwardCollapse_naturality]
  rfl

def paddedCollapseNat : forwardFunctor ⋙ paddingFunctor ⟶
    (Functor.const Word).obj threeArrow where
  app := paddedCollapse
  naturality _ _ f := by
    change paddingFunctor.map (forwardMap f) ≫ paddedCollapse _ = paddedCollapse _ ≫ 𝟙 _
    rw [Category.comp_id, paddedCollapse_naturality]

end SerrePositivity.EInfinity.Hammock.Word
