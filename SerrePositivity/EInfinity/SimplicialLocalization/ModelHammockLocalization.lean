module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantLocalization
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelHammockNerveEquivalence
public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeHammockSourceComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationEquivalenceTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakDeformationSource
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent

/-!
概要：実 bifibrant hammock の局所化普遍性を同じ cofibrant 部分圏と全モデル圏へ戻す。
方針：Ind-S (6) の源移送を元の弱単位・余単位へ適用し、同じ hammock nerve 同値を消去する。
規約：第一の関手的分解と指定 right frame のみを使い、元の源写像を保持する。
使われ方：全 C または cofibrant 部分圏の指定局所化への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対関手の nerve は同じ弱射の辺集合を保つ。
方針：元の射の全 simplex 表示を同じ関手で送る。
規約：元の指定弱辺。使われ方：Ind の源移送への入力。 -/
lemma relativeNerve_mapsWeak {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{w}}
    (F : LocalizerMorphism A.weakEquivalences B.weakEquivalences)
    (s : (nerve A.category) _⦋1⦌) (hs : s ∈ weakNerveEdges A) :
    (nerveMap F.functor).app (Opposite.op ⦋1⦌) s ∈ weakNerveEdges B := by
  obtain ⟨X, Y, f, hf, rfl⟩ := hs
  exact ⟨F.functor.obj X, F.functor.obj Y, F.functor.map f, F.map f hf,
    by simpa using nerveMap_app_mk₁ F.functor f⟩

/-- 概要：同じ弱自然変換の nerve ホモトピーの全成分は元の弱辺。
方針：同じ元の成分辺の厳密な回収を使う。
規約：元のホモトピーの向きを変えない。使われ方：単位・余単位の源移送。 -/
lemma relativeNerve_homotopy_component_weak {A : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{w}}
    {F G : A.category ⥤ A.category} (η : F ⟶ G)
    (hη : ∀ X, A.weakEquivalences (η.app X)) (x : (nerve A.category) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η) x).edge ∈ weakNerveEdges A := by
  obtain ⟨X, rfl⟩ : ∃ X : A.category, x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X :=
    ⟨x.obj 0, ComposableArrows.ext₀ rfl⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component]
  exact ⟨F.obj X, G.obj X, η.app X, hη X, rfl⟩

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

include r in
/-- 概要：同じ cofibrant 部分圏の実 hammock は元の弱同値による ∞ 局所化。
方針：同じ right frame の二つの弱単位に Ind の逆向き源移送を適用する。
規約：同じ元の nerve 源写像を最後に回収する。
使われ方：cofibrant 源の指定局所化と全 C への移送。 -/
lemma modelCofibrantHammock_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C))
      (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_weakDeformation_reverse
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative (C := C)).functor)
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r).functor)
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C))
    (relativeNerve_mapsWeak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative (C := C)))
    (relativeNerve_mapsWeak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantBifibrantUnit r))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantCofibrantUnit r))
    (relativeNerve_homotopy_component_weak _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantBifibrantUnit_weak r))
    (relativeNerve_homotopy_component_weak _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantCofibrantUnit_weak r))
    (modelBifibrantHammock_isLocalization r)
  rw [← relativeKanHammockNerve_source] at ht
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_comp_equivalence_iff _ _
    (hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C))
    (modelCofibrantToBifibrant_nerve_isQCatEquivalence r).choose).mp ht

include r in
/-- 概要：同じ全モデル圏の実 hammock は元の弱同値による ∞ 局所化。
方針：同じ第一分解の二つの弱余単位に Ind の源移送を適用する。
規約：全 C と元の全射を保持し、source の cofibrancy を要求しない。
使われ方：指定全圏局所化の pinched Hom と実 frame の全比較。 -/
lemma modelHammock_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
      (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_weakDeformation
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C).functor)
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C).functor)
    (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (relativeNerve_mapsWeak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C))
    (relativeNerve_mapsWeak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit C))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit C))
    (relativeNerve_homotopy_component_weak _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit_weak C))
    (relativeNerve_homotopy_component_weak _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit_weak C))
    (modelCofibrantHammock_isLocalization r)
  rw [← relativeKanHammockNerve_source] at ht
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_comp_equivalence_iff _ _
    (hammockLocalizationNerveMap_inverts (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (modelToCofibrant_nerve_isQCatEquivalence C).choose).mp ht

end SerrePositivity.EInfinity.SimplicialLocalization

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.15" (partial := stronger-hyp) "仮定：モデル圏の cofibrant 対象と弱同値、hammock の構成には関手的分解と指定フレーム（Lean が強い：一般の定義だけなら追加データは不要）。結論：その通常の nerve を弱同値で局所化して underlying ∞ 圏の具体模型を得る（一致する場合）。"] _root_.SerrePositivity.EInfinity.SimplicialLocalization.modelCofibrantHammock_isLocalization
attribute [cite HA "1.3.4.16" (partial := component) "仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：明示的な hammock 模型とフレームを選ぶ）。結論：全圏・cofibrant 圏・cf 圏の局所化を、置換の比較を使って構成する（Lean が弱い：fibrant だけの部分圏はこの型に含まれない）。"] _root_.SerrePositivity.EInfinity.SimplicialLocalization.modelCofibrantHammock_isLocalization
attribute [cite HA "1.3.4.16" (partial := component) "仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：明示的な hammock 模型とフレームを選ぶ）。結論：全圏・cofibrant 圏・cf 圏の局所化を、置換の比較を使って構成する（Lean が弱い：fibrant だけの部分圏はこの型に含まれない）。"] _root_.SerrePositivity.EInfinity.SimplicialLocalization.modelHammock_isLocalization
attribute [cite HA "1.3.4.20" (partial := stronger-hyp) "仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：HA の単体モデル圏と構成された θ をそのまま入力しない）。結論：cofibrant 及び cf の通常の nerve の弱同値による局所化を hammock で得る（Lean が弱い：θ の標的である cf の豊穣 coherent nerve との指定比較がこの型にない）。"] _root_.SerrePositivity.EInfinity.SimplicialLocalization.modelCofibrantHammock_isLocalization
attribute [cite HA "4.1.7.3" (partial := special) "仮定：C はモデル圏の通常の nerve で、W は弱同値。関手的分解と指定フレームを要求する（Lean が強い：一般の準圏と system を扱わない）。結論：指定された弱同値を反転する普遍的な C[W⁻¹] の模型（一致する特殊例。全 system に対する左随伴の構成は型にない）。"] _root_.SerrePositivity.EInfinity.SimplicialLocalization.modelHammock_isLocalization
