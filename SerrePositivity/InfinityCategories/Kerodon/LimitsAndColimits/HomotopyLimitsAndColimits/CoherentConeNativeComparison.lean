module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeApexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentLeftHomComparison

/-!
概要：任意の coherent な豊穣錐の反転 Hom から native な切断の制限への比較を構成する。
方針：頂点評価の厳密な切断を選び、coslice fiber の標準比較を錐の図式上へ持ち上げる。
規約：切断の選択を含む。Bousfield–Kan の比較 q′ との一致はこの定義には含めない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の豊穣比較と極限錐の接続。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {C : Type v} [Category.{u} C]
  [SimplicialCategory C]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 概要：任意の coherent な錐の図式上の切断を指定した頂点の対象で評価する。
方針：一般の頂点評価を、任意の coherent な錐の頂点の等号で正規化する。
規約：終域は x の coslice の z 上の fiber。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の豊穣 Hom 比較の始域の正規化。 -/
noncomputable def coherentConeApexEvaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneApexSectionEvaluation c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) ≫
    eqToHom (congrArg (fun y : (SimplicialNerve C) _⦋0⦌ ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))) y)
      hz)

/-- 概要：頂点を正規化した評価も、包含後には通常の内部 Hom の頂点評価になる。
方針：頂点の等式による移送を消去し、一般の錐の評価式を使う。
規約：全パラメータでの厳密な射の等式。
使われ方：HTT 4.2.4.1 の具体的な持ち上げの頂点条件の検証。 -/
lemma coherentConeApexEvaluation_ι (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    coherentConeApexEvaluation c z hz x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) K)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex K) := by
  have ht {E B : SSet.{max u v}} (q : E ⟶ B) {y y' : B _⦋0⦌} (h : y = y') :
      eqToHom (congrArg (fun b : B _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y' =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q y := by cases h; exact Category.id_comp _
  rw [coherentConeApexEvaluation, Category.assoc, ht _ hz, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneApexSectionEvaluation_ι]

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：局所 Kan な単体的圏の任意の coherent な錐の頂点評価は trivial Kan fibration。
方針：一般の頂点評価に、頂点の等号による同型を合成する。
規約：元の錐の極限性や図式の fibration 性は要求しない。
使われ方：HTT 4.2.4.1 の豊穣 Hom を始域とする切断比較の構成。 -/
lemma coherentConeApexEvaluation_trivialKanFibration (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (coherentConeApexEvaluation c z hz x) := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneApexSectionEvaluation_trivialKanFibration
      c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：任意の coherent な錐の頂点評価の厳密な切断。
方針：trivial Kan fibration の切断の存在から一つ選ぶ。
規約：切断の選択の図式に関する自然性は主張しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の Hom の族を錐の図式上の切断へ持ち上げる射。 -/
noncomputable def coherentConeApexSection (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) := by
  have := coherentConeApexEvaluation_trivialKanFibration c z hz x
  exact Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (coherentConeApexEvaluation c z hz x))

/-- 概要：選んだ切断に続く頂点評価は元の coslice fiber の恒等射。
方針：切断を選んだ存在命題の等式を回収する。
規約：ホモトピーではなく厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の豊穣比較の頂点での値の追跡。 -/
lemma coherentConeApexSection_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    coherentConeApexSection c z hz x ≫ coherentConeApexEvaluation c z hz x = 𝟙 _ := by
  have := coherentConeApexEvaluation_trivialKanFibration c z hz x
  exact Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (coherentConeApexEvaluation c z hz x))

/-- 概要：反転した豊穣 Hom の族を任意の coherent な錐の図式上の切断へ持ち上げる比較。
方針：coslice fiber の標準比較に、頂点評価の選んだ切断を合成する。
規約：始域は宇宙を持ち上げた sHom(x,z).op。
使われ方：HTT 4.2.4.1 の豊穣 Hom と native な錐の切断の接続。 -/
noncomputable def reflectedCoherentConeFamilyComparison (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z ≫ coherentConeApexSection c z hz x

/-- 概要：豊穣 Hom から錐の図式上への比較を頂点で評価すると標準の coslice 比較になる。
方針：選んだ切断と評価の厳密な合成則を使う。
規約：全 Hom パラメータの射の等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の比較の始域の同値性の検査。 -/
lemma reflectedCoherentConeFamilyComparison_evaluation (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    reflectedCoherentConeFamilyComparison c z hz x ≫ coherentConeApexEvaluation c z hz x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x z := by
  rw [reflectedCoherentConeFamilyComparison, Category.assoc,
    coherentConeApexSection_evaluation, Category.comp_id]

/-- 概要：豊穣 Hom から任意の coherent な錐の図式上の切断への比較はホモトピー同値。
方針：頂点での標準比較と trivial Kan な評価から二対三則を使う。
規約：Hom の局所 Kan 性のみで、錐の極限性は仮定しない。
使われ方：HTT 4.2.4.1 の native な制限の判定の始域を豊穣 Hom に置く準備。 -/
lemma reflectedCoherentConeFamilyComparison_homotopyEquivalence (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (reflectedCoherentConeFamilyComparison c z hz x) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)
  have := coherentConeApexEvaluation_trivialKanFibration c z hz x
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentConeApexEvaluation c z hz x) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (coherentConeApexEvaluation c z hz x)).isQCatEquivalence
  apply (he.cancel_right ?_).isSimplicialHomotopyEquivalence
  rw [reflectedCoherentConeFamilyComparison_evaluation]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison_homotopyEquivalence x z).isQCatEquivalence

/-- 概要：反転した豊穣 Hom から元の図式上の切断への native な比較。
方針：錐の図式上への持ち上げに、元の図式への実際の制限を合成する。
規約：Bousfield–Kan の q′ との同定は別工程。
使われ方：HTT 4.2.4.1 の任意の coherent な錐の極限性の豊穣 Hom による判定。 -/
noncomputable def reflectedCoherentNativeConeComparison (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) :=
  reflectedCoherentConeFamilyComparison c z hz x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)

/-- 概要：任意の coherent な錐の極限性は、各豊穣 Hom からの native な比較の同値性で検出できる。
方針：任意の nerve の頂点を元の対象で表示し、始域の標準比較に二対三則を使う。
規約：添字単体集合と coherent な錐は任意。q′ との比較の仮定は含めない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の通常の Hom 極限との照合の入力。 -/
lemma coherentCone_isLimit_iff_reflectedNativeComparison (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (z : C) (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (reflectedCoherentNativeConeComparison c z hz x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_coneSectionRestriction_homotopyEquivalence]
  constructor
  · intro h x
    exact (reflectedCoherentConeFamilyComparison_homotopyEquivalence c z hz x).comp
      (h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
  · intro h z
    obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).surjective z
    have hs :=
      (reflectedCoherentConeFamilyComparison_homotopyEquivalence c z hz x).isQCatEquivalence
    exact (hs.cancel_left (h x).isQCatEquivalence).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
