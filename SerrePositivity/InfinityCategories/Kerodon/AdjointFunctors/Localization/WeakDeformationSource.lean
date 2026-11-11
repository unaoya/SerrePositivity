module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization

/-!
概要：指定辺集合を保つ弱変形に沿って、一般の局所化の源を移送する。
方針：反転関手圏の制限を相互逆にし、元の局所化の全前合成同値と合成する。
規約：源・標的の quasicategory 性を要求せず、既存の変形局所化定理は変更しない。
使われ方：Ind-S (6)、E2-S (6) の bifibrant 源から元の源への局所化移送。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace WeakDeformationSource

/-- 概要：反転関手圏の指定頂点を表す実関手の反転条件。
方針：頂点表示の同値を消去する。規約：標的の充填性は不要。
使われ方：制限と全ホモトピー比較の点条件。 -/
lemma vertex_inverts {A E : SSet.{u}} {W : Set (A _⦋1⦌)}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E W : SSet.{u}) _⦋0⦌) (f : A ⟶ E)
    (hf : v.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges f W := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm v.val) W at h
  rw [hf] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E) f)) W at h
  simpa only [Equiv.symm_apply_apply] using h

/-- 概要：指定辺を保つ射に沿う反転関手族の制限。
方針：実前合成を反転関手の全部分複体へ持ち上げる。
規約：源・標的の充填性は不要。使われ方：弱変形の相互逆となる全族射。 -/
def restriction {A B : SSet.{u}} (f : A ⟶ B)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hf : ∀ s ∈ WA, f.app (Opposite.op ⦋1⦌) s ∈ WB) (E : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex A E WA)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι ≫ (pre f).app E) (by
      intro v
      obtain ⟨g, hg⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B E).surjective v.val
      have hv := vertex_inverts v g hg.symm
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm
        (((pre f).app E).app (Opposite.op ⦋0⦌) v.val)) WA
      rw [← hg]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E) (f ≫ g))) WA
      rw [Equiv.symm_apply_apply]
      intro s hs
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
        (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map g))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (f ≫ g))) rfl).mp (hv (hf s hs)))

/-- 概要：制限は元の全前合成を厳密に回収する。
方針：全部分複体への持ち上げの包含公式。規約：同じ実射の等号。
使われ方：二つの制限の合成と局所化前合成の照合。 -/
lemma restriction_ι {A B : SSet.{u}} (f : A ⟶ B)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hf : ∀ s ∈ WA, f.app (Opposite.op ⦋1⦌) s ∈ WB) (E : SSet.{u}) :
    restriction f WA WB hf E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι ≫ (pre f).app E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：指定辺成分を持つ任意の向きのホモトピーは反転関手族上で同型。
方針：全前合成ホモトピーを反転関手族へ制限し、各点の反転条件を適用する。
規約：ホモトピーを逆転させない。使われ方：逆向き弱変形からの単位・余単位。 -/
def invertingHomotopyIso {A : SSet.{u}} {f g : A ⟶ A} (W : Set (A _⦋1⦌))
    (H : SSet.Homotopy f g) (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E W).ι ≫ (pre f).app E)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E W).ι ≫ (pre g).app E) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoRestrictedPrecompositionOfHomotopy H (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E W).ι (by
    intro v k hk x
    have h := vertex_inverts v k hk
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge).map ((truncation 2).map k))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated.map ((truncation 2).map k)) rfl).mp
        (h (hH x)))

/-- 概要：二つの制限の合成に対する全変形同型から反転関手圏の同値を作る。
方針：全部分複体への包含による充満忠実性で同じ比較同型を持ち上げる。
規約：比較は全関手同型として保持する。使われ方：局所化源の移送の中間同値。 -/
def restrictionEquivalence {A B : SSet.{u}} (i : A ⟶ B) (r : B ⟶ A)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hi : ∀ s ∈ WA, i.app (Opposite.op ⦋1⦌) s ∈ WB)
    (hr : ∀ s ∈ WB, r.app (Opposite.op ⦋1⦌) s ∈ WA)
    (E : SSet.{u}) [Quasicategory E]
    (eA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι ≫ (pre (i ≫ r)).app E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι)
    (eB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι ≫ (pre (r ≫ i)).app E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB : SSet.{u}) where
  hom := restriction r WB WA hr E
  inv := restriction i WA WB hi E
  homInvIso := by
    let ff := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA : SSet.{u}) ((ihom A).obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex A E WA)
    apply ff.preimageIso
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((restriction r WB WA hr E ≫ restriction i WA WB hi E) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι) ((𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι)
    rw [Category.assoc, restriction_ι, ← Category.assoc, restriction_ι, Category.id_comp]
    simpa only [pre_map, NatTrans.comp_app, Category.assoc] using eA
  invHomIso := by
    let ff := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB : SSet.{u}) ((ihom B).obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex B E WB)
    apply ff.preimageIso
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((restriction i WA WB hi E ≫ restriction r WB WA hr E) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι) ((𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι)
    rw [Category.assoc, restriction_ι, ← Category.assoc, restriction_ι, Category.id_comp]
    simpa only [pre_map, NatTrans.comp_app, Category.assoc] using eB

/-- 概要：反転関手圏の制限同値を元の局所化と合成する。
方針：包含後の厳密等号で合成を同じ局所化前合成に同定する。
規約：源と局所化標的の充填性は不要。使われ方：両向きの弱変形版の共通本体。 -/
lemma transfer {A B D : SSet.{u}} (i : A ⟶ B) (r : B ⟶ A) (q : A ⟶ D)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hi : ∀ s ∈ WA, i.app (Opposite.op ⦋1⦌) s ∈ WB)
    (hr : ∀ s ∈ WB, r.app (Opposite.op ⦋1⦌) s ∈ WA)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q WA)
    (hA : ∀ (E : SSet.{u}) [Quasicategory E],
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι ≫ (pre (i ≫ r)).app E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors A E WA).ι))
    (hB : ∀ (E : SSet.{u}) [Quasicategory E],
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι ≫ (pre (r ≫ i)).app E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (r ≫ q) WB := by
  have hqr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (r ≫ q) WB := by
    intro s hs
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (r.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map q))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (r ≫ q))) rfl).mp (hq.choose (hr s hs))
  refine ⟨hqr, fun E _ => ?_⟩
  let e := restrictionEquivalence i r WA WB hi hr E (hA E).some (hB E).some
  have he := (hq.choose_spec E).comp e.isQCatEquivalence
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q WA hq.choose E ≫ restriction r WB WA hr E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (r ≫ q) WB hqr E := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors B E WB).ι).1
    rw [Category.assoc, restriction_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι]
    simp only [pre_map, NatTrans.comp_app]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q WA hq.choose E ≫
    restriction r WB WA hr E) at he
  rw [hc] at he
  exact he

end WeakDeformationSource

/-- 概要：指定弱辺成分による両側変形に沿って局所化源を移送する。
方針：反転関手族上で両変形を同型にし、元の局所化同値へ合成する。
規約：A・B・D の quasicategory 性は不要。使われ方：E2-S (6) の弱変形による復帰。 -/
theorem isLocalization_of_weakDeformation {A B D : SSet.{u}}
    (i : A ⟶ B) (r : B ⟶ A) (q : A ⟶ D)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hi : ∀ s ∈ WA, i.app (Opposite.op ⦋1⦌) s ∈ WB)
    (hr : ∀ s ∈ WB, r.app (Opposite.op ⦋1⦌) s ∈ WA)
    (H : SSet.Homotopy (r ≫ i) (𝟙 B))
    (K : SSet.Homotopy (i ≫ r) (𝟙 A))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ WB)
    (hK : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge ∈ WA)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q WA) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (r ≫ q) WB :=
  WeakDeformationSource.transfer i r q WA WB hi hr hq
    (fun E _ => ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization.deformationLocalizationInvertingIso i r WA K hK E⟩)
    (fun E _ => ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization.deformationLocalizationInvertingIso r i WB H hH E⟩)

/-- 概要：恒等射から合成への指定弱変形でも局所化源を移送する。
方針：反転関手族上で得た全同型を逆にし、同じ制限同値を使う。
規約：元のホモトピーの逆転や源の充填性は仮定しない。使われ方：E2 の逆向き置換単位。 -/
theorem isLocalization_of_weakDeformation_reverse {A B D : SSet.{u}}
    (i : A ⟶ B) (r : B ⟶ A) (q : A ⟶ D)
    (WA : Set (A _⦋1⦌)) (WB : Set (B _⦋1⦌))
    (hi : ∀ s ∈ WA, i.app (Opposite.op ⦋1⦌) s ∈ WB)
    (hr : ∀ s ∈ WB, r.app (Opposite.op ⦋1⦌) s ∈ WA)
    (H : SSet.Homotopy (𝟙 B) (r ≫ i))
    (K : SSet.Homotopy (𝟙 A) (i ≫ r))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ WB)
    (hK : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge ∈ WA)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q WA) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (r ≫ q) WB := by
  apply WeakDeformationSource.transfer i r q WA WB hi hr hq
  · intro E _
    have e := (WeakDeformationSource.invertingHomotopyIso WA K hK E).symm
    simpa only [pre_id, NatTrans.id_app, Category.comp_id] using Nonempty.intro e
  · intro E _
    have e := (WeakDeformationSource.invertingHomotopyIso WB H hH E).symm
    simpa only [pre_id, NatTrans.id_app, Category.comp_id] using Nonempty.intro e

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
