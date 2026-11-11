module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftInputComposition
/-!
概要：共通対象宇宙の入力持ち上げの前合成・合成等式を、元の nerve の厳密等式にする。
方針：既存の dg 関手等式に nerve を適用し、同じ二段合成を展開する。
規約：元の入力写像を保持する。使われ方：unlifted 分解比較の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v w))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] in
/-- 元の入力 Up と持ち上げた入力の合成は、元の入力 nerve と次の Up の合成に一致する。 -/
lemma dgUniverseLift_sourcePrecomp_nerve (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B) := by
  have h := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_sourcePrecomp.{u, v, w} R A B H)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using h
/-- 二つの持ち上げた実入力写像の nerve の合成は、同じ合成入力の持ち上げの nerve。 -/
lemma dgUniverseLift_inputPrecomp_comp_nerve (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (J : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R B))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R B).comp
        (J.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        ((H.comp J).comp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) := by
  have h := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_inputPrecomp_comp.{u, max (u + 1) v w, w} R A B C H J)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
