module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedCosliceLinearCoordinates
/-!
概要：同じ実 coslice fiber の閉前合成を、左 Hom の同じ鎖写像作用へ厳密に同定する。
方針：全線形座標の単射性で全写像を照合し、準同型不変性を実 fiber 射へ戻す。
規約：対象の小ささも前三角性も不要。使われ方：Hom 関手族の実 fiber 同値の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (x q y : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
/-- 実 fiber の左 Hom 表示は、同じ標準 Hom 前合成鎖写像の作用に等しい。 -/
lemma dgCoslicePrecomposeLeftMap_eq_chainMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D D
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R D q y n).injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap_linear R D x q y s t).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap_linear R D D _ t).symm
lemma dgCoslicePrecomposeLeftMap_isQCatEquivalence
    [QuasiIso (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeLeftMap R D x q y s) := by
  rw [dgCoslicePrecomposeLeftMap_eq_chainMap]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap_isQCatEquivalence R D D _
lemma dgCoslicePrecomposeFiber_isQCatEquivalence
    [QuasiIso (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeFiber R D x q y s) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
  have H := dgCoslicePrecomposeLeftMap_isQCatEquivalence R D x q y s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoslicePrecomposeFiber R D x q y s ≫ f.inv)) at H
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso f.symm).isQCatEquivalence.cancel_right
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.cancel_left H)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
