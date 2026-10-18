module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeApexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedRepresentableComparison

/-!
概要：strict な豊穣錐の反転 Hom から native な切断の制限への比較を構成する。
方針：頂点評価の厳密な切断を選び、coslice fiber の標準比較を錐の図式上へ持ち上げる。
規約：切断の選択を含む。Bousfield–Kan の比較 q′ との一致はこの定義には含めない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6、7.5.4.6 の豊穣比較と極限錐の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：strict な錐の図式上の切断を元の錐の対象で評価する。
方針：一般の頂点評価を、strict な錐の頂点の等号で正規化する。
規約：終域は x の coslice の c.pt 上の fiber。
使われ方：Kerodon 7.5.4.6 の豊穣 Hom 比較の始域の正規化。 -/
noncomputable def strictConeApexEvaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x) ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex c.pt) :=
  coneApexSectionEvaluation (strictCoherentCone c) (coherentNerveVertex x) ≫
    eqToHom (congrArg (fun y : (SimplicialNerve C) _⦋0⦌ ↦
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))) y)
      (strictCoherentCone_vertex c))

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：局所 Kan な単体的圏の strict な錐の頂点評価は trivial Kan fibration。
方針：一般の頂点評価に、頂点の等号による同型を合成する。
規約：元の錐の極限性や図式の fibration 性は要求しない。
使われ方：HTT 4.2.4.1 の豊穣 Hom を始域とする切断比較の構成。 -/
lemma strictConeApexEvaluation_trivialKanFibration {F : I ⥤ C} (c : Cone F) (x : C) :
    TrivialKanFibration (strictConeApexEvaluation c x) := by
  exact ⟨trivialKanFibrations.comp_mem _ _
    (coneApexSectionEvaluation_trivialKanFibration
      (strictCoherentCone c) (coherentNerveVertex x)).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：strict な錐の頂点評価の厳密な切断。
方針：trivial Kan fibration の切断の存在から一つ選ぶ。
規約：切断の選択の図式に関する自然性は主張しない。
使われ方：Kerodon 7.5.4.6 の Hom の族を錐の図式上の切断へ持ち上げる射。 -/
noncomputable def strictConeApexSection {F : I ⥤ C} (c : Cone F) (x : C) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex c.pt) ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x) := by
  have := strictConeApexEvaluation_trivialKanFibration c x
  exact Classical.choose (trivialKanFibration_exists_section (strictConeApexEvaluation c x))

/-- 概要：選んだ切断に続く頂点評価は元の coslice fiber の恒等射。
方針：切断を選んだ存在命題の等式を回収する。
規約：ホモトピーではなく厳密な等式。
使われ方：Kerodon 7.5.4.6 の豊穣比較の頂点での値の追跡。 -/
lemma strictConeApexSection_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    strictConeApexSection c x ≫ strictConeApexEvaluation c x = 𝟙 _ := by
  have := strictConeApexEvaluation_trivialKanFibration c x
  exact Classical.choose_spec (trivialKanFibration_exists_section (strictConeApexEvaluation c x))

/-- 概要：反転した豊穣 Hom の族を strict な錐の図式上の切断へ持ち上げる比較。
方針：coslice fiber の標準比較に、頂点評価の選んだ切断を合成する。
規約：始域は宇宙を持ち上げた sHom(x,c.pt).op。
使われ方：HTT 4.2.4.1 の豊穣 Hom と native な錐の切断の接続。 -/
noncomputable def reflectedStrictConeFamilyComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x) :=
  coherentCosliceFiberComparison x c.pt ≫ strictConeApexSection c x

/-- 概要：豊穣 Hom から錐の図式上への比較を頂点で評価すると標準の coslice 比較になる。
方針：選んだ切断と評価の厳密な合成則を使う。
規約：全 Hom パラメータの射の等式。
使われ方：Kerodon 7.5.4.6 の比較の始域の同値性の検査。 -/
lemma reflectedStrictConeFamilyComparison_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    reflectedStrictConeFamilyComparison c x ≫ strictConeApexEvaluation c x =
      coherentCosliceFiberComparison x c.pt := by
  rw [reflectedStrictConeFamilyComparison, Category.assoc,
    strictConeApexSection_evaluation, Category.comp_id]

/-- 概要：豊穣 Hom から strict な錐の図式上の切断への比較はホモトピー同値。
方針：頂点での標準比較と trivial Kan な評価から二対三則を使う。
規約：Hom の局所 Kan 性のみで、錐の極限性は仮定しない。
使われ方：HTT 4.2.4.1 の native な制限の判定の始域を豊穣 Hom に置く準備。 -/
lemma reflectedStrictConeFamilyComparison_homotopyEquivalence {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeFamilyComparison c x) := by
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex c.pt)
  have := strictConeApexEvaluation_trivialKanFibration c x
  have he : IsQCatEquivalence (strictConeApexEvaluation c x) :=
    (qCatEquivalenceOfTrivialKanFibration (strictConeApexEvaluation c x)).isQCatEquivalence
  apply (he.cancel_right ?_).isSimplicialHomotopyEquivalence
  rw [reflectedStrictConeFamilyComparison_evaluation]
  exact (coherentCosliceFiberComparison_homotopyEquivalence x c.pt).isQCatEquivalence

/-- 概要：反転した豊穣 Hom から元の図式上の切断への native な比較。
方針：錐の図式上への持ち上げに、元の図式への実際の制限を合成する。
規約：Bousfield–Kan の q′ との同定は別工程。
使われ方：HTT 4.2.4.1 の strict な錐の極限性の豊穣 Hom による判定。 -/
noncomputable def reflectedNativeConeComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x) :=
  reflectedStrictConeFamilyComparison c x ≫
    coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x)

/-- 概要：strict な錐の極限性は、各豊穣 Hom からの native な比較の同値性で検出できる。
方針：任意の nerve の頂点を元の対象で表示し、始域の標準比較に二対三則を使う。
規約：添字圏と strict な錐は任意。q′ との比較の仮定は含めない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の通常の Hom 極限との照合の入力。 -/
lemma strictCoherentCone_isLimit_iff_reflectedNativeConeComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (reflectedNativeConeComparison c x) := by
  rw [isLimitCone_iff_coneSectionRestriction_homotopyEquivalence]
  constructor
  · intro h x
    exact (reflectedStrictConeFamilyComparison_homotopyEquivalence c x).comp
      (h (coherentNerveVertex x))
  · intro h z
    obtain ⟨x, rfl⟩ := (coherentNerveVertexEquiv C).surjective z
    have hs := (reflectedStrictConeFamilyComparison_homotopyEquivalence c x).isQCatEquivalence
    exact (hs.cancel_left (h x).isQCatEquivalence).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
