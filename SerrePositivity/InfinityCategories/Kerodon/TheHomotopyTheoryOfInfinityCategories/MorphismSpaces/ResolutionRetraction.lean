module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionCylinder

/-!
概要：Kan 複体から解像の右随伴への比較射の厳密な左逆。
方針：解像の射影を比較射の像に沿って貼り合わせ、余単位を延長する。
規約：単体集合の pushout のみを使い、モデル構造は使わない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 4.6.7.16（Tag 01LQ）、比較射の同値性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：比較射を解像で写して余単位に続けると解像の射影になる。
方針：随伴対応とその逆の合成が恒等であることを使う。
規約：Kan 性を要求しない随伴の式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、余単位の貼り合わせ条件。 -/
lemma coherentResolutionComparison_counit (Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.counit.app Z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Z := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv Z Z).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv Z Z (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Z)) = _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv Z Z).symm_apply_apply _

/-- 概要：Kan 複体の比較射には厳密な左逆が存在する。
方針：射影の pushout 上に余単位を貼り、前合成の同値で延長後、単射上で厳密化する。
規約：左逆との合成はホモトピーだけでなく射の等式として成立する。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射のホモトピー逆の構成。 -/
lemma coherentResolutionComparison_exists_retraction (Z : SSet.{u}) [KanComplex Z] :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z ⟶ Z,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z ≫ c = 𝟙 Z := by
  let χ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map χ
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Z
  let L := pushout i r
  let k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) ⟶ L := pushout.inl i r
  let j : Z ⟶ L := pushout.inr i r
  have hn : i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) =
      r ≫ χ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality χ
  let q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z :=
    pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z)) χ hn
  have hkq : k ≫ q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) := by
    exact pushout.inl_desc _ _ _
  have hjq : j ≫ q = χ := by exact pushout.inr_desc _ _ _
  have hk : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence k :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence Z).of_isPushout_of_mono_other
      (IsPushout.of_hasPushout i r).flip
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence q := hk.cancel_left (by
    rw [hkq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence _)
  let a : L ⟶ Z := pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.counit.app Z) (𝟙 Z) (by
    exact (coherentResolutionComparison_counit Z).trans (Category.comp_id r).symm)
  have hja : j ≫ a = 𝟙 Z := by exact pushout.inr_desc _ _ _
  obtain ⟨v, ⟨e⟩⟩ := (hq Z).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  obtain ⟨c₀, rfl⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) Z).surjective v
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ c₀) a := e
  have e'' := e'.precomp j
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (χ ≫ c₀) (𝟙 Z) := by
    simpa only [← Category.assoc, hjq, hja] using e''
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_extension_of_functorIso χ c₀ (𝟙 Z) he

/-- 概要：Kan 複体から解像の右随伴への比較射は quasicategory の同値。
方針：厳密な左逆と転置で得た右逆を可逆二胞体で比較する。
規約：右随伴の Kan 性を使い、両合成の可逆二胞体を構成する。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、coherent nerve の写像空間の比較。 -/
lemma coherentResolutionComparison_isQCatEquivalence (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z) := by
  obtain ⟨c, hc⟩ := coherentResolutionComparison_exists_retraction Z
  obtain ⟨b, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_postcomp_essentiallySurjective
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z))
  have ebc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c := by
    simpa only [Category.assoc, hc, Category.comp_id, Category.id_comp] using e.postcomp c
  refine ⟨c, ⟨?_⟩, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp ebc.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z)) ≪≫ e⟩⟩
  rw [hc]

/-- 概要：Kan 複体の比較射は単体的ホモトピー同値。
方針：quasicategory の同値の可逆二胞体を Kan 標的のホモトピーで表す。
規約：Kan 複体間の射として同値を述べる。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、写像空間の比較の宇宙の持ち上げ。 -/
lemma coherentResolutionComparison_isSimplicialHomotopyEquivalence
    (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z) :=
  (coherentResolutionComparison_isQCatEquivalence Z).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
