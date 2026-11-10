module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ScaffoldFiberMaps

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveLeftFibration
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 値図式から left fibration への scaffold の条件と二つの標準例。
方針：底上の可換性と各係数値からの fiber 比較の同値性を組み合わせる。
規約：left fibration では全ての辺が cocartesian なので、水平辺の条件は自動的に満たされる。
使われ方：Kerodon Definition 5.3.4.2、Propositions 5.3.4.8、5.3.4.17、全体比較の仮定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 値図式から left fibration への射が scaffold であるという条件。
方針：底上の可換性と、指定した全ての係数値の fiber 比較が同値であることを要求する。
規約：水平辺の像の cocartesian 性は p の left fibration 性から従う。
使われ方：Kerodon Definition 5.3.4.2、left fibration の全空間の比較の入力。 -/
def IsLeftScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) : Prop :=
  ∃ h : l ≫ p = simplicialReplacementProjection F,
    ∀ c, IsQCatEquivalence (leftScaffoldFiberMap p F l h c)

/-- 概要：Kan 値図式の taut scaffold は left scaffold の条件を満たす。
方針：底の可換性と、係数値から weighted nerve の fiber への標準同型を使う。
規約：全空間の同値はこの時点では結論に含めない。
使われ方：Kerodon Proposition 5.3.4.17、復元候補との比較の標準例。 -/
@[kerodon 0379]
lemma tautScaffold_isLeftScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] :
    IsLeftScaffold (weightedNerveProjection F) F (tautScaffold F) := by
  refine ⟨tautScaffold_projection F, fun c ↦ ?_⟩
  have he : leftScaffoldFiberMap (weightedNerveProjection F) F (tautScaffold F)
      (tautScaffold_projection F) c = weightedNerveFiberMap F c := by
    apply vertexFiber_hom_ext
    exact simplicialReplacementConstantLift_tautScaffold F c
  rw [he]
  exact (qCatEquivalenceOfIso (weightedNerveFiberIso F c)).isQCatEquivalence

/-- 概要：left fibration の strict transport 図式の係数値は Kan 複体。
方針：strict transport の Kan 性を単体集合値図式の対象に対する型クラスとして提供する。
規約：係数を忘れた通常の図式にも同じ Kan 性を用いる。
使われ方：Kerodon Construction 5.3.1.5、universal scaffold の係数条件。 -/
instance leftStrictTransportDiagram_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    KanComplex ((leftStrictTransportDiagram p).obj c) := leftStrictTransport_kanComplex p c

/-- 概要：left fibration の universal scaffold は left scaffold の条件を満たす。
方針：係数値の fiber 比較を恒等射の評価と同定し、その trivial Kan fibration 性を使う。
規約：元の全空間の quasicategory 性は通常の nerve 上の left fibration 性から得られる。
使われ方：Kerodon Proposition 5.3.4.8、元の全空間との比較の標準例。 -/
@[kerodon 0370]
lemma universalScaffold_isLeftScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsLeftScaffold p (leftStrictTransportDiagram p) (universalScaffold p) := by
  refine ⟨universalScaffold_projection p, fun c ↦ ?_⟩
  have he : leftScaffoldFiberMap p (leftStrictTransportDiagram p) (universalScaffold p)
      (universalScaffold_projection p) c = leftStrictTransportEvaluate p c := by
    apply vertexFiber_hom_ext
    exact simplicialReplacementConstantLift_universalScaffold p c
  rw [he]
  exact leftStrictTransportEvaluate_isQCatEquivalence p c

end SerrePositivity.InfinityCategories
