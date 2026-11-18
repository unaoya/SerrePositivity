module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanHomChainMaps

/-!
# 元の標準 Hom の Moore 正規化と鎖写像の各成分

概要：元の正規化部分対象での射は、具体的線形単体の同じ成分写像となる。
方針：実 Moore 包含の自然性と元の項同型の包含公式を使う。
規約：正規化の射・包含・全成分を元のまま保つ。
使われ方：実 Γ 比較の Hom 鎖写像への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

lemma normalizedMoore_map_arrow {W V : SimplicialObject (ModuleCat.{u} R)}
    (f : W ⟶ V) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat R)).map f).f n ≫
      (NormalizedMooreComplex.objX V n).arrow =
    (NormalizedMooreComplex.objX W n).arrow ≫ f.app (Opposite.op (SimplexCategory.mk n)) := by
  simp [normalizedMooreComplex, NormalizedMooreComplex.map]

lemma standardMooreTermIso_map_val (f : homObject R D x y ⟶ homObject R E x' y') (n : ℕ)
    (s : ((normalizedMooreComplex (ModuleCat R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X n) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x' y' n).hom
      (((normalizedMooreComplex (ModuleCat R)).map (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)).f n s))).val =
    (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f).app (Opposite.op (SimplexCategory.mk n))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y n).hom s).val) := by
  have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.ComplexLimits.normalizedMoore_map_arrow (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f) n) s
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso_hom_subtype x' y', ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso_hom_subtype x y] at h
  exact h

lemma standardMooreTermIso_map_component (f : homObject R D x y ⟶ homObject R E x' y')
    (n : ℕ) (s : ((normalizedMooreComplex (ModuleCat R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x' y' n).hom
        (((normalizedMooreComplex (ModuleCat R)).map (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)).f n s)).val.val)
      J k hJ hk =
    f.f k ((((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y n).hom s).val).val.component J k hJ hk) := by
  rw [_root_.SerrePositivity.ComplexLimits.standardMooreTermIso_map_val, _root_.SerrePositivity.ComplexLimits.standardModuleChainMap_val]
  rfl

end SerrePositivity.ComplexLimits
