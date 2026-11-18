module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanNormalizationComponents
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanTruncationMaps

/-!
# 元の標準正規化同型の任意の Hom 鎖写像への自然性

概要：同じ標準模型の Moore 写像と smart 切断写像は元の正規化同型と可換。
方針：零次数では cycles の包含、正次数では項同型の後で全体集合成分を比較する。
規約：元の standardNormalizationIso の同じ射を保つ。
使われ方：実 Γ Hom 比較の鎖写像への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

lemma standardNormalizationIso_chainMap
    (f : homObject R D x y ⟶ homObject R E x' y') :
    (normalizedMooreComplex (ModuleCat R)).map (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x' y').hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom ≫
      truncLE'Map f (ComplexShape.embeddingUpIntLE 0) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  cases n with
  | zero =>
    apply (ModuleCat.mono_iff_injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').hom ≫
        (homObject R E x' y').iCycles 0)).mp inferInstance
    change (homObject R E x' y').iCycles 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').hom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x' y').hom.f 0
          (((normalizedMooreComplex (ModuleCat R)).map (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)).f 0 s))) =
      (homObject R E x' y').iCycles 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').hom
        ((truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f 0
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0 s)))
    rw [_root_.SerrePositivity.ComplexLimits.standardNormalizationIso_zero_eval]
    have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.ComplexLimits.connectiveHomComplex_zero_chainMap f)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0 s)
    change (homObject R E x' y').iCycles 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x' y').hom
        ((truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f 0
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0 s))) =
      f.f 0 ((homObject R D x y).iCycles 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0 s))) at h
    rw [h, _root_.SerrePositivity.ComplexLimits.standardNormalizationIso_zero_eval]
    exact _root_.SerrePositivity.ComplexLimits.standardMooreTermIso_map_component f 0 s Finset.univ 0 Finset.univ_nonempty (by simp)
  | succ n =>
    apply (ModuleCat.mono_iff_injective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).hom).mp inferInstance
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).hom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x' y').hom.f (n + 1)
          (((normalizedMooreComplex (ModuleCat R)).map (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f)).f (n + 1) s)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).hom
        ((truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f (n + 1)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f (n + 1) s))
    rw [_root_.SerrePositivity.ComplexLimits.standardNormalizationIso_positive_eval]
    have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.ComplexLimits.connectiveHomComplex_positive_chainMap f n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f (n + 1) s)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x' y' n).hom
        ((truncLE'Map f (ComplexShape.embeddingUpIntLE 0)).f (n + 1)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f (n + 1) s)) =
      f.f (-(n + 1 : ℤ)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x y n).hom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f (n + 1) s)) at h
    rw [h, _root_.SerrePositivity.ComplexLimits.standardNormalizationIso_positive_eval]
    exact _root_.SerrePositivity.ComplexLimits.standardMooreTermIso_map_component f (n + 1) s Finset.univ (-(n + 1 : ℤ))
      Finset.univ_nonempty (by simp)

end SerrePositivity.ComplexLimits
