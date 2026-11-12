module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedPropertyStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullFunctorRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullInclusionExactReflection
/-!
概要：標準演算で閉じる加群部分圏間への実 dg 関手の完全性。
方針：周囲の dg 関手の完全性と、元の包含との厳密な可換性を使う。
規約：像の対象条件の閉性は反映には不要。使われ方：β5 の Perf の実完全包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 演算で閉じた始域の加群部分圏への実 dg 制限は、全 cofiber 列を保存する。 -/
theorem dgClosedModuleFunctorNerve_isExactFunctor
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (P : _root_.SerrePositivity.DifferentialGraded.RightModule R D → Prop) (Q : _root_.SerrePositivity.DifferentialGraded.RightModule R E → Prop)
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedProperty R D P) (hF : ∀ M, P M → Q (F.obj M)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction R _ _ F P Q hF)) := by
  let I := _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) P
  let J := _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) Q
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction R _ _ F P Q hF
  have hd : G.comp J = I.comp F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction_inclusion R _ _ F P Q hF
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) hd
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleInclusion_isExactFunctor R D P hP
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor R D E F
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J) :=
    he.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isExactFunctor_of_postcomp_dgFullInclusion R (RightModule R E) Q (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
