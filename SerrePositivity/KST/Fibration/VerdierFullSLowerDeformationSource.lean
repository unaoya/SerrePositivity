module

public import SerrePositivity.KST.Fibration.VerdierFullSLowerDeformation
public import SerrePositivity.KST.Fibration.VerdierLowerTriangleZeroHom

/-!
概要：元の下側二胞体の変形を Stable∞ で行ってから全 S• Kan 作用へ送る。
方針：同じ path 変形と元の豊穣関手の後合成を、全単体上で厳密に照合する。
規約：指定二胞体と全変形を保持する。上側との共有対角比較はまだ主張しない。
使われ方：K-6 c4 で元の零値 Hom の制御を保ちながら下側変形を使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：元の Stable∞ 下側二胞体の全変形の像は、既存の全 S• Kan 下側変形そのもの。
方針：各単体で同じ path 変形の豊穣後合成を照合する。
規約：端点や長辺だけでなく全三角柱の等式。
使われ方：元の零値完全関手の Hom 制御を同じ下側変形へ移す。 -/
theorem verdierFullSLowerDeformation_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformationMap (verdierLowerTriangle d) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0) =
        (verdierFullSLowerDeformation d).h := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  rfl

/-- 概要：元の Stable∞ 下側二胞体の最大化の像は同じ全 S• Kan 最大化の全二胞体。
方針：最大 path の元の豊穣後合成を照合する。
規約：元の指定包含・商を変えず、標準合成端全体を保持する。
使われ方：元の実商核の標準合成二胞体との比較。 -/
theorem verdierFullSLowerMaximalization_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋2⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierLowerTriangle d)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d) := rfl

/-- 概要：同じ全三角柱の動く対角も、元の Stable∞ 対角族の同じ像である。
方針：全三角柱の等式を元の対角面で前合成する。
規約：動く対角を定値と主張しない。
使われ方：上側の同じ対角族との貼り合わせに使う指定制限。 -/
theorem verdierFullSLowerDeformation_diagonal_source :
    ((stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformationMap (verdierLowerTriangle d)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0) =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSLowerDeformation d).h := by
  rw [Category.assoc, verdierFullSLowerDeformation_source]

end SerrePositivity.KST.Fibration
