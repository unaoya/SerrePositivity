module

public import SerrePositivity.BhattScholze.Perfectoidization.Interface.CAlg.Comparison

/-!
# 既存 CAlg_R 上の BS 界面

概要：G1 の算術的データを保ち、指定極限と excision を CAlg_R で述べる。
方針：単位は実離散埋め込みからの全関手射、底は実 U との合成とする。
規約：指定錐の底との比較は全錐の同型で保持し、極限性を D(R) の入力にしない。
使われ方：文献入力を述べ直す際の型と、D(R) 版の証明済みの系。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Perfectoidization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

/-- 概要：CAlg_R の指定錐と、元の単位・H⁰ の乗法を保つ底の比較データ。
方針：既存 BSLimitConeData の非普遍的データを使い、全錐比較を加える。
規約：底の錐の極限性は欄に含めない。全標的・全単体の比較を保持する。
使われ方：実 U の極限保存を同じ指定錐へ適用する。 -/
structure BSLimitConeDataCAlg (P : algebraNerve R ⟶ CAlg_R R)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (algebraEmbedding R) P)
    (h0 : H0RingData R (P ≫ cAlgForgetDerived R) (underlyingUnit R η)) (S : A_R R) where
  /-- 同じ perfectoid 標的図式上の CAlg_R 錐。 -/
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (targetCAlgDiagram R p S)
  /-- 錐頂点は元の P(S)。 -/
  vertex_eq : cone.vertex = P.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)
  /-- 元の単位と H⁰ の全射影の乗法整合性。 -/
  underlying : BSLimitConeData R p (P ≫ cAlgForgetDerived R) (underlyingUnit R η) h0 S
  /-- 通常の S 上の錐からの CAlg_R の比較辺。 -/
  overSource : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (targetCAlgDiagram R p S)).Edge
    (underlying.sourceCone.postcomp (algebraEmbedding R)) cone
  /-- 同じ CAlg_R 単位の実代表を保つ。 -/
  overSource_unit : (overSource.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (targetCAlgDiagram R p S))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)).edge
  /-- U 像と既存 G1 の指定錐の全関手比較。 -/
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cone.val ≫ cAlgForgetDerived R) underlying.cone.val
  /-- 標的図式上の比較は完成済みの離散比較自身。 -/
  comparison_boundary : HEq
    (comparison.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (perfectoidTargetNerve p S.right)))
    (targetCAlgDiagramForgetIso R p S)
  /-- 頂点上では同じ P(S) の恒等比較。 -/
  comparison_vertex : HEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app comparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (perfectoidTargetNerve p S.right)).app _ (SSet.yonedaEquiv (𝟙 Δ[0]))))
    (Iso.refl (SSet.HomotopyCategory.mk (vertex R (P ≫ cAlgForgetDerived R) S)))

/-- 概要：G1 の結論を既存の CAlg_R で述べた BS 界面。
方針：指定極限・excision は CAlg_R、算術条件は同じ U と H⁰ で述べる。
規約：通常の非完備代数を含む。存在・文献入力・animated 環の構成は追加しない。
使われ方：toE3 により旧 D(R) 界面とその下流へ供給する。 -/
structure PerfectoidizationInterfaceCAlg (hR : IsIntegralPerfectoid R p) where
  perfd : algebraNerve R ⟶ CAlg_R R
  unit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (algebraEmbedding R) perfd
  h0 : H0RingData R (perfd ≫ cAlgForgetDerived R) (underlyingUnit R unit)
  universal : ∀ S, IsDiscrete R (perfd.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)) →
    IsPerfectoidization p (h0.unit.app S).right.hom
  limitCone : ∀ S, BSLimitConeDataCAlg R p perfd unit h0 S
  limit_isLimit : ∀ S, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (limitCone S).cone
  integral : ∀ (S : A_R R),
    (letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) →
    IsDiscrete R (perfd.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)) ∧
      IsIntegralPerfectoid (h0.ringFunctor.obj S).right p
  excision : ∀ {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right),
    SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right S.right) →
    SerrePositivity.DerivedCompletion.IsModuleComplete T.right (p : T.right)
      (ModuleCat.of T.right T.right) →
    SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right I) →
    ArcOutside R p f I →
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R f (quotientProjection R S I)
      (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
      (quotientSquare_commutes R f I) ≫ perfd)

end SerrePositivity.EInfinity.Perfectoidization
