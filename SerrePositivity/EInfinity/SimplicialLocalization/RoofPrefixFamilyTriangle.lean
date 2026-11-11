module
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismOne
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismZeroSlice
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismProjection
public import SerrePositivity.EInfinity.SimplicialLocalization.HammockInvertsEdges
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinched
public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismFamilyComposition
/-! 概要：任意の同じ宇宙の相対列の roof 全族の評価三角形。
方針：元の slice prism の両端と射影を全関手圏の合成へ移す。
規約：元の全添字・左右脚と実 Kan hammock を保持する。
使われ方：自由 E∞ 列の全 pinched 族の大域比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

/-- 概要：元の roof 全族を同じ coherent 頂点の pinched Hom に送る。
方針：同じ Hom 比較へ合成。規約：全単体を保持。
使われ方：元の slice prism の一端。 -/
def coherentPinchedFamily : nerve I ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y)) :=
  familyMap C U p hp σ hU ≫ (kanHammockHomLiftIso C X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison ((kanHammockSourceFunctor C).obj X)
      ((kanHammockSourceFunctor C).obj Y)

/-- 概要：実 prism の一端は元の coherent pinched 全族。
方針：全単体の実 cochain に対応する coherent Hom の値を比較する。
規約：全要素を保持。使われ方：評価三角形の一端。 -/
lemma prism_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve I) ≫ prism C U p hp σ hU =
    coherentPinchedFamily C U p hp σ hU ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice (kanHammockNerve C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (simplex C U p hp σ hU Γ (OrderHom.const _ 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (((coherentPinchedFamily C U p hp σ hU).app (Opposite.op ⦋n⦌) Γ).val)
  rw [simplex_one C U p hp σ hU Γ]
  rfl

/-- 概要：実 prism の一端の評価は同じ全区間族。
方針：pinched slice の評価公式を使う。規約：全パラメータを保持。
使われ方：全関手圏の合成。 -/
lemma prism_one_evaluation :
    (β_ (nerve I) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ prism C U p hp σ hU) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (coherentPinchedFamily C U p hp σ hU ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)).h := by
  rw [prism_one C U p hp σ hU]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))
    (coherentPinchedFamily C U p hp σ hU ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice _ _ _)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_pinched_h (coherentPinchedFamily C U p hp σ hU))

/-- 概要：元の通常自然変換の円柱を同じ coherent 頂点へ送る。
方針：実局所化源の頂点公式で終端だけを表示し直す。
規約：円柱全体を保持。使われ方：全 roof 三角形の二辺。 -/
def coherentAugmentationHomotopy {Z : C.category}
    (a : U ⟶ (Functor.const I).obj Z) :
    SSet.Homotopy (nerveMap U ≫ hammockLocalizationNerveMap C)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Z))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (FrameHom.FrameArrows.augmentationHomotopy U a (hammockLocalizationNerveMap C)) rfl
    (congrArg (fun z => SSet.const (X := nerve I) z)
      (hammockLocalizationNerveMap_vertex C Z))

/-- 概要：元の全 roof 族と両通常円柱の全関手圏の合成関係。
方針：実 slice prism の二端と射影を既存の合成判定へ代入する。
規約：同じ全添字と元の左右脚を保持。使われ方：標準単位の全族比較。 -/
lemma family_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (coherentAugmentationHomotopy C U p)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (coherentPinchedFamily C U p hp σ hU ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (coherentAugmentationHomotopy C U σ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.slicePrismFamily_comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))
    (coherentAugmentationHomotopy C U p) (coherentAugmentationHomotopy C U σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (coherentPinchedFamily C U p hp σ hU ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) (prism C U p hp σ hU)
  · exact prism_zero_evaluation C U p hp σ hU
  · exact prism_one_evaluation C U p hp σ hU
  · rw [prism_projection C U p hp σ hU, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
    rfl

/-- 概要：同じ弱 augmentation の円柱は全関手同型。
方針：各元の弱射の反転性を全円柱の判定へ代入する。
規約：元の円柱自身を使う。使われ方：全 roof の左脚の反転。 -/
def coherentAugmentationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap U ≫ hammockLocalizationNerveMap C)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj X))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (coherentAugmentationHomotopy C U p)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentAugmentationHomotopy C U p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge =
      ((nerve.edgeMk (p.app i)).map (hammockLocalizationNerveMap C)).edge := by
    change (hammockLocalizationNerveMap C).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge) = _
    exact congrArg ((hammockLocalizationNerveMap C).app _)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component p i)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := ((nerve.edgeMk (p.app i)).map (hammockLocalizationNerveMap C)).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ (p.app i))).map
      ((SSet.truncation 2).map (hammockLocalizationNerveMap C))) rfl).mpr
    (hammockLocalizationNerveMap_inverts C ⟨_, _, p.app i, hp i, rfl⟩)

/-- 概要：元の全 pinched roof は同じ augmentation の逆と評価の合成。
方針：全評価三角形の左脚を反転する。
規約：全関手圏で比較。使われ方：元の導来 roof との接続。 -/
lemma family_eq_roof : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (coherentPinchedFamily C U p hp σ hU ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    (coherentAugmentationIso C U p hp).inv ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (coherentAugmentationHomotopy C U σ)) := by
  apply (cancel_epi (coherentAugmentationIso C U p hp).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact family_comp C U p hp σ hU

private lemma endpoint_family_arrow {K E : SSet.{u}} {a b a' b' : E _⦋0⦌}
    (ha : a = a') (hb : b = b') (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom ((f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso ha hb).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace a' b')) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace a b)) := by
  subst a'
  subst b'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso, Iso.refl_hom, Category.comp_id]

/-- 概要：実局所化源の端点表示でも元の全 roof 自身を回収する。
方針：同じ端点等式の輸送を Arrow 等式で保持する。
規約：全族と両端表示を保持。使われ方：CAlg_R への後合成比較。 -/
lemma native_family_eq_roof_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom ((familyMap C U p hp σ hU ≫
      kanHammockHomPinchedMap C X Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk ((coherentAugmentationIso C U p hp).inv ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (coherentAugmentationHomotopy C U σ))) := by
  have h := endpoint_family_arrow
    (hammockLocalizationNerveMap_vertex C X).symm
    (hammockLocalizationNerveMap_vertex C Y).symm (coherentPinchedFamily C U p hp σ hU)
  have he : familyMap C U p hp σ hU ≫ kanHammockHomPinchedMap C X Y =
      coherentPinchedFamily C U p hp σ hU ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (hammockLocalizationNerveMap_vertex C X).symm
          (hammockLocalizationNerveMap_vertex C Y).symm).hom := by
    simp only [kanHammockHomPinchedMap, coherentPinchedFamily, Category.assoc]
  rw [he]
  exact h.trans (congrArg Arrow.mk (family_eq_roof C U p hp σ hU))

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
