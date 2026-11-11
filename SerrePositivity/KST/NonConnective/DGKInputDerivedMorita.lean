module
public import SerrePositivity.KST.NonConnective.DGKInputDerivedCompactGeneration
public import SerrePositivity.KST.NonConnective.DGKappaPerfectMapMorita

/-!
概要：元の主 Perf 延長の同値性を、同じ実 dg 射の全主導来同値性へ広げる。
方針：両側の実小 Perf 生成族と元の導来随伴による余積保存を Morita 判定へ代入する。
規約：全主導来同値を追加仮定にせず、元の厳密射を保持する。
使われ方：K-7 e の実懸垂 Morita 保存を反復するための接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type (max (u + 1) v))
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (f : DGFunctor R C D)

/-- 元の主 Perf 延長の同値性は、同じ主導来延長の同値性を与える。 -/
theorem dgKInputDerivedExtension_isEquivalence_of_perfect
    [(quasiEquivalencePerfectExtension R C D f).IsEquivalence] :
    (dgDerivedExtension R C D f).IsEquivalence := by
  let := dgDerivedExtensionCommShift R C D f
  let := dgDerivedExtensionIsTriangulated R C D f
  let := (dgDerivedExtensionRestrictionAdjunction R C D f).leftAdjoint_preservesColimits
  let hperf : ∀ X, modulePerfect R C X →
      modulePerfect R D ((dgDerivedExtension R C D f).obj X) :=
    fun _ h => dgDerivedExtension_perfect R C D f h
  let : (Morita.perfectFunctorRestriction R C D (dgDerivedExtension R C D f)
      hperf).IsEquivalence := by
    change (quasiEquivalencePerfectExtension R C D f).IsEquivalence
    infer_instance
  exact Morita.criterionDerivedIsEquivalence_of_perfectEquivalence R C D _ hperf
    (dgKInputDerivedCompactFamily R C) (dgKInputDerivedCompactGeneration R C)
    (dgKInputDerivedCompactFamily R D) (dgKInputDerivedCompactGeneration R D)
    (fun _ => inferInstance)

/-- 前三角な実 dg 射の native 同値性は同じ主導来 Morita 同値を与える。 -/
theorem dgKInputDerivedExtension_isEquivalence_of_native
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map f)) :
    (dgDerivedExtension R C D f).IsEquivalence := by
  let := dgKappaPerfectExtension_isEquivalence_of_native R C D f hf
  exact dgKInputDerivedExtension_isEquivalence_of_perfect R C D f

end SerrePositivity.KST.NonConnective
