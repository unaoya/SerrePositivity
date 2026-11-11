module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedInfinity
/-!
概要：元の同じ入力から元の半自由模型への実 ∞ 関手を、指定比較射に沿って比較する。
方針：同じ分解変更の全関手同型へ、元の対象宇宙の上げ下げを前後合成する。
規約：元の出力の射影性を要求しない。使われ方：任意双加群の実導来作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
/-- 全 Hom 自然な次数別全射準同型に沿う、元の実半自由出力 ∞ 関手の全関手同型。 -/
def dgModuleResolvedInfinity_changeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E G) := by
  have e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_changeIso R C E a hs hq ha).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity, Category.assoc] using e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
