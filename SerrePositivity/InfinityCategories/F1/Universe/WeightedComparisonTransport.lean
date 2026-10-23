module

public import SerrePositivity.InfinityCategories.F1.Universe.WeightedTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection

/-!
概要：持ち上げた weighted nerve の比較射を介し、係数の射と標的の transport を比較する。
方針：持ち上げた係数輸送と底上の射に関する transport の自然性を合成する。
規約：底は元の nerve の宇宙持ち上げであり、coherent な復元の比較と同じ宇宙に置く。
使われ方：Kerodon Corollary 5.6.0.6、strict な Kan 図式とその unstraightening の射への作用の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：持ち上げた係数値から、全空間の比較射の標的 fiber への射。
方針：係数値の標準 fiber 同型と比較射の fiber への作用を合成する。
規約：比較射は持ち上げた底の nerve を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元の値での比較の射。 -/
noncomputable def uliftWeightedNerveComparisonFiber {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{max u v}}
    (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C))
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F)) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ⟶ vertexFiber q (ULift.up (nerveVertex c)) :=
  (uliftWeightedNerveFiberIso.{u, v} F c).hom ≫
    vertexFiberMap ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F)) q h hh
      (ULift.up (nerveVertex c))

/-- 概要：持ち上げた係数の射と比較先の transport は fiber の比較射を介して関手同型まで可換。
方針：持ち上げた係数での標準 transport の同定と、全空間の射に関する自然性を合成する。
規約：同型は持ち上げた F(c) から比較先の終点 fiber への射の間で取る。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元で元の Kan 複体の射を回収する。 -/
noncomputable def uliftWeightedNerveComparisonFiber_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map (F.map f) ≫ uliftWeightedNerveComparisonFiber F q h hh d)
      (uliftWeightedNerveComparisonFiber F q h hh c ≫
        edgeTransport q (uliftTruncatedEdge.{u, v} (nerve.edgeMk f))) := by
  have e₀ := FunctorIso.postcomp (uliftWeightedNerveTransport_coefficientIso.{u, v} F f).symm
    ((uliftWeightedNerveFiberIso.{u, v} F d).hom ≫
      vertexFiberMap ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F)) q h hh
        (ULift.up (nerveVertex d)))
  have e₁ := FunctorIso.precomp
    (leftFibrationMap_transportIso ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
      q h hh (uliftTruncatedEdge.{u, v} (nerve.edgeMk f)))
    (uliftWeightedNerveFiberIso.{u, v} F c).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at e₀
  exact e₀ ≪≫ e₁

/-- 概要：全空間の前合成同値から、持ち上げた係数と標的 fiber の比較の同値性を得る。
方針：相対逆による fiber 同値の回収に標準 fiber 同型を合成する。
規約：底の持ち上げた nerve は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6、選択した復元比較の値での同値性。 -/
lemma uliftWeightedNerveComparisonFiber_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    (eh : IsPrecompositionEquivalence h) (c : C) :
    IsQCatEquivalence (uliftWeightedNerveComparisonFiber F q h hh c) :=
  (qCatEquivalenceOfIso (uliftWeightedNerveFiberIso.{u, v} F c)).isQCatEquivalence.comp
    (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F)) q h hh eh
      (ULift.up (nerveVertex c)))

/-- 概要：持ち上げた weighted nerve と同値な標的の transport の同値性は持ち上げた係数の射で判定できる。
方針：全空間の同値から両端の fiber 同値を回収し、transport の自然性に二対三則を使う。
規約：比較射 h は底を保つ前合成同値。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元の transport の同値性を検出する。 -/
lemma uliftWeightedNerveComparison_transport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    (eh : IsPrecompositionEquivalence h) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport q (uliftTruncatedEdge.{u, v} (nerve.edgeMk f))) ↔
      IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map (F.map f)) := by
  have hc := uliftWeightedNerveComparisonFiber_isQCatEquivalence F q h hh eh c
  have hd := uliftWeightedNerveComparisonFiber_isQCatEquivalence F q h hh eh d
  have e := uliftWeightedNerveComparisonFiber_transportIso F q h hh f
  exact ⟨fun he ↦ hd.cancel_right ((hc.comp he).ofFunctorIso e.symm),
    fun he ↦ hc.cancel_left ((he.comp hd).ofFunctorIso e)⟩

end SerrePositivity.InfinityCategories
