module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGPretriangulatedFunctorLiftedExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseExactFunctor

/-! # 前三角 dg 圏間の native nerve の関手の完全性

概要：前三角 dg 圏間の任意の dg 関手の元の宇宙の nerve は完全。
方針：対象宇宙を上げた関手を実宇宙同型で照合し、零対象と cofiber 保存を降下する。
規約：平坦性や模型圏の仮定を追加しない。使われ方：β3 の実商関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

omit [Small.{u} D] [Small.{u} E] in
/-- 対象宇宙を上げた dg 関手は、実宇宙同型で元の nerve の ULift に一致。 -/
lemma dgUniverseLiftFunctor_nerve_conjugate :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso A E).inv =
      (SSet.uliftFunctor.{max (u + 1) v, max u v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  ext n s
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl

/-- 前三角 dg 圏間の任意の dg 関手の native nerve は完全。 -/
theorem dgPretriangulatedFunctor_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_ulift.{max u v, max (u + 1) v}
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctorLifted_isExactFunctor A D E F
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D)).isQCatEquivalence
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A E).symm).isQCatEquivalence
  rw [← dgUniverseLiftFunctor_nerve_conjugate A D E F]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
