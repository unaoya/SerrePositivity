module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedStrictification

/-!
# 正規化 Moore 関手の加法性

概要：正規化 Moore 関手が射の和を保つことを証明する。
方針：正規化射を包含・交代面複体の射・射影で挟む公式へ移し、加法性を合成する。
規約：KST Construction A.5 の augmentation 補正、任意のアーベル圏。
使われ方：三つの補正項の鎖ホモトピーを和と差で合成する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory AlgebraicTopology

/-- 概要：正規化 Moore 関手は加法関手。
方針：包含と射影で挟む公式と交代面複体の加法性を使う。
規約：KST A.5、追加の加法性仮定を要求しない。
使われ方：C(φ)+C(φ′)−C(e) の補正を正規化した鎖写像へ移す。 -/
instance normalizedMooreComplex_additive {A : Type u} [Category.{v} A] [Abelian A] :
    (normalizedMooreComplex A).Additive where
  map_add {X Y f g} := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_eq_retract (f + g), CategoryTheory.Functor.map_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_eq_retract f, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedMap_eq_retract g]

end SerrePositivity.KST.ProExcision
