module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.DirectKanUnstraightening
public import SerrePositivity.InfinityCategories.F1.Universe.WeightedComparisonTransport
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection

/-!
概要：strict な Kan 値図式の coherent な unstraightening の transport から元の係数の射を回収する。
方針：既存の直接復元比較に、持ち上げた weighted nerve の transport の自然性を適用する。
規約：係数値の宇宙は u、復元の全空間と fiber は u+1。
使われ方：Kerodon Corollary 5.6.0.6、選択済み unstraightening の作用と通常の Kan 複体の射の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：直接復元比較が与える、係数の Kan 複体から復元の fiber への比較射。
方針：持ち上げた weighted nerve の標準 fiber 同型に直接復元比較の fiber 射を合成する。
規約：係数値を u+1 に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6、strict な図式の復元の値での比較。 -/
noncomputable def directKanUnstraighteningFiberComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (F.obj c).obj ⟶
      vertexFiber (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (ULift.up (nerveVertex c)) :=
  uliftWeightedNerveComparisonFiber (F ⋙ kanObjectForget)
    (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
    (directKanUnstraighteningComparison F) (directKanUnstraighteningComparison_projection F) c

/-- 概要：直接復元比較による各係数値と復元の fiber の比較射は同値。
方針：直接復元比較の前合成同値性から各 fiber の同値を回収する。
規約：選択した比較射そのものの性質として述べる。
使われ方：Kerodon Corollary 5.6.0.6、図式の射への作用を比較する両端の同値。 -/
lemma directKanUnstraighteningFiberComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    IsQCatEquivalence (directKanUnstraighteningFiberComparison F c) := by
  let : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c ↦ (F.obj c).isKanComplex
  exact uliftWeightedNerveComparisonFiber_isQCatEquivalence (F ⋙ kanObjectForget)
    (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
    (directKanUnstraighteningComparison F) (directKanUnstraighteningComparison_projection F)
    (directKanUnstraighteningComparison_isPrecompositionEquivalence F) c

/-- 概要：strict な図式の係数の射と coherent な復元の標準 transport は、値の同値を介して関手同型まで可換。
方針：直接復元比較に、持ち上げた weighted nerve の transport の自然性を適用する。
規約：係数の射は任意で、同値であるとは仮定しない。
使われ方：Kerodon Corollary 5.6.0.6、coherent な unstraightening の作用を元の図式の射で同定する。 -/
noncomputable def directKanUnstraighteningFiberComparison_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫
        directKanUnstraighteningFiberComparison F d)
      (directKanUnstraighteningFiberComparison F c ≫
        edgeTransport (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f))) := by
  let : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c ↦ (F.obj c).isKanComplex
  exact uliftWeightedNerveComparisonFiber_transportIso (F ⋙ kanObjectForget)
    (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
    (directKanUnstraighteningComparison F) (directKanUnstraighteningComparison_projection F) f

/-- 概要：strict な図式の coherent な復元の transport の同値性は、元の係数の射で判定できる。
方針：直接復元比較の transport の判定と、Kan 複体の同値性の宇宙持ち上げによる反映を使う。
規約：比較先は元の宇宙の F.map f そのもの。
使われ方：Kerodon Corollary 5.6.0.6、復元側の辺の作用の同値性を検出する。 -/
lemma directKanUnstraighteningTransport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence
      (edgeTransport (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f))) ↔
      IsQCatEquivalence (F.map f) := by
  let : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c ↦ (F.obj c).isKanComplex
  exact (uliftWeightedNerveComparison_transport_isQCatEquivalence_iff (F ⋙ kanObjectForget)
    (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
    (directKanUnstraighteningComparison F) (directKanUnstraighteningComparison_projection F)
    (directKanUnstraighteningComparison_isPrecompositionEquivalence F) f).trans
      (isQCatEquivalence_ulift_iff_of_kan.{u, u + 1} (F.map f))

end SerrePositivity.InfinityCategories
