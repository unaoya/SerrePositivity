module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeSmallHomContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeContravariantHomContinuity
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：小さい錐の宇宙反映を使い随伴関手定理の宇宙比較入力を除去する。
方針：Hom 模型の連続性と accessibility を元の宇宙へ戻して全随伴を構成する。
規約：充満忠実性を仮定しない。余極限保存側の表現可能局所性比較だけを明示する。
使われ方：d5 の無条件判定と d4 の残る局所性比較への接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全 Yoneda Hom 合成の元の filtered 保存から Ind 値の関手の保存性を反映する。
方針：小さい各評価の保存性を回収し、元の指定像余錐の各点普遍性を検査する。
規約：μ と κ の間に順序や交換条件を仮定しない。
使われ方：共通 Hom 濃度による右随伴の元の accessibility の判定。 -/
lemma isKappaAccessibleFunctor_of_indHomTests_native
    (κ μ : Cardinal.{u})
    (A : SSet.{u}) [Quasicategory A] {D : SSet.{u + 1}}
    (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)
    (hG : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} μ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G := by
  intro I hI hμ F c hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_fullyFaithful_image (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf_isFullyFaithful κ A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_isColimit_of_evaluation _ _
  intro a
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation a
  have ht := (hG a).of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomCompositeIso G
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)) H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indYonedaHom_evaluationIso κ A a))
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (G ≫ H) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaAccessibleFunctor_of_spaceUniverse_image ht
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (by
    simp only [H, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc])).mpr (hn I F c hc)


/-- 概要：accessible 圏の右随伴は accessible。
方針：小さい生成 Hom 族を共通の正則濃度で保存し、Ind の各点検出で元の保存性へ戻す。
規約：右随伴の保存性や compact 性を追加入力にしない。
使われ方：無条件の宇宙反映界面を適用する随伴関手定理の必要方向。 -/
@[kerodon 06LC]
lemma rightAdjoint_isAccessible
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D)
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor R := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hA
  let a' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (e.hom ≫ L) (R ≫ e.inv) := e.toAdjunction.comp a
  obtain ⟨μ, hμ, _, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.adjunction_exists_common_hom_preservationCardinal a' hD
    (fun x : A _⦋0⦌ ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up x)) κ
  have hR' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (R ≫ e.inv) :=
    isKappaAccessibleFunctor_of_indHomTests_native κ μ A (R ≫ e.inv) ht
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((R ≫ e.inv) ≫ e.hom) R := by
    simpa only [Category.assoc, Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.invHomIso R
  exact ⟨μ, hμ, (hR'.comp
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ e.isQCatEquivalence)).of_functorIso he⟩


/-- 概要：accessible な極限保存関手の各 Hom 合成の小さい連続模型を得る。
方針：元の Hom の小さい模型を合成し、同じ濃度と極限保存を反映する。
規約：宇宙変更の反映は構成済みであり、追加の比較入力を要求しない。
使われ方：元の小さい Hom による随伴関手定理の接続。 -/
lemma accessible_limitPreservingHomModels
    {X Y : SSet.{u + 1}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible X)
    (G : Y ⟶ X) (hGa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor G) (hGl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits G) :
    ∀ x : X _⦋0⦌, ∃ H : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits H ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
          ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) := by
  intro x
  obtain ⟨H, ⟨hH⟩⟩ := hX.exists_smallCovariantHom x
  exact ⟨G ≫ H, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_isAccessible_native hX G hGa x H hH,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_preservesSmallLimits_native G hGl x H hH, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomCompositeIso G x H hH⟩⟩


/-- 概要：presentable 圏の右随伴は accessible な小極限保存関手と同値。
方針：必要方向は右随伴の保存と Hom 濃度、十分方向は小さい Hom 模型の余表現を使う。
規約：指定宇宙変更の小さい錐の反映を使い、充満忠実性を仮定しない。
使われ方：presentable 圏の右随伴関手の判定。 -/
@[kerodon 06Q5]
lemma exists_leftAdjoint_iff_accessible_preservesLimits
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (R : D ⟶ C) :
    (∃ L : C ⟶ D, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits R := by
  constructor
  · rintro ⟨L, ⟨a⟩⟩
    exact ⟨rightAdjoint_isAccessible
      hC.isAccessible hD.isAccessible a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.adjunction_preservesSmallLimits a⟩
  · rintro ⟨hRa, hRl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_of_accessible_limitPreserving_HomModels R
      hD.isAccessible hD.hasSmallLimits
      (accessible_limitPreservingHomModels
        hC.isAccessible R hRa hRl)


/-- 概要：連続前層の表現定理から余極限保存関手の右随伴を構成する。
方針：各小さい反変 Hom 合成を表現し、全自然比較から反対圏の随伴を戻す。
規約：入力の表現定理は元の始域上の全ての小さい空間値連続前層を対象とする。
使われ方：d4 の存在方向の接続。 -/
lemma exists_rightAdjoint_of_colimitPreserving_representability_native
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible Y)
    (hRep : ∀ H : X.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits H →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor H) (L : X ⟶ Y) (hL : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L) :
    ∃ R : Y ⟶ X, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.exists_rightAdjoint_of_contravariantHom_representable L
  intro y
  obtain ⟨H, ⟨hH⟩⟩ := hY.exists_smallContravariantHom y
  obtain ⟨x, ⟨hx⟩⟩ := hRep (SSet.opFunctor.map L ≫ H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallContravariantHomComposite_sendsSmallColimitsToLimits_native L hL y H hH)
  refine ⟨x, ⟨hx ≪≫ ?_⟩⟩
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp hH
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h.symm

/-- 概要：連続前層の表現定理の下で右随伴の存在は小余極限保存と同値。
方針：存在方向を小さい Hom 模型で構成し、必要方向は全随伴の余極限保存を使う。
規約：一般の d2 の表現定理のみを入力とする。
使われ方：d2 の表現定理から d4 の公開判定への接続。 -/
lemma exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible Y)
    (hRep : ∀ H : X.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits H →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor H) (L : X ⟶ Y) :
    (∃ R : Y ⟶ X, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L := by
  constructor
  · rintro ⟨R, ⟨a⟩⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits a
  · exact exists_rightAdjoint_of_colimitPreserving_representability_native hY hRep L


/-- 概要：表現可能局所性の比較界面の下で presentable 圏の左随伴は小余極限保存と同値。
方針：反映による連続前層の表現定理を、右随伴の構成へ入力する。
規約：局所性比較の存在は主張せず、元の全関手の全随伴を結論する。
使われ方：F1 の局所性比較による d4 の最終接続。 -/
lemma exists_rightAdjoint_iff_preservesSmallColimits_of_inversionLocality
    (hLocal : ∀ (A : SSet.{u}) [Quasicategory A],
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentableInversionDetectsLocality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A))
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (L : C ⟶ D) :
    (∃ R : D ⟶ C, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L :=
  exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native hD.isAccessible
    (fun F hF ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableContinuous_isRepresentable_of_inversionLocality hLocal hC F hF) L

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.6.1" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：原典の任意の準圏にこの仮定を追加）。結論：左右随伴の存在で頂点を選ぶ FunL(C,D),FunR(C,D) の全部分準圏（この場合に一致）。PrL は全小余極限保存、PrR は accessible かつ全小極限保存で定義され、二つの存在判定の同値により同じ頂点条件となる。core だけには制限していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits
attribute [cite HTT "5.2.6.2" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：任意の準圏の場合は含まない）。結論：FunL(C,D) と FunR(D,C)op の全準圏の同値で、同値の順方向の各値は元の左関手の右随伴（この場合に一致）。PrL/PrR の頂点条件と随伴存在の同値も併用する。非可逆な自然変換と全高次単体を保持し、右随伴の対象ごとの選択だけでは代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits
attribute [cite HTT "5.4.7.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible
attribute [cite HTT "5.5.1.1" (partial := direction) "仮定：presentable な準圏 C（HTT と一致）。結論：小準圏 A の前層圏からの反映表示 L⊣R と R の充満忠実性、L の全小余極限保存を構成し、R も accessible（(1)⇒(5) に一致）。(2)(3) の全 κ-small compact 余極限や (4)(6) との全ての同値はこの宣言群にない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible
attribute [cite HTT "5.5.1.2" (partial := direction) "仮定：accessible C と accessible D への反映 f⊣g、および元の L≃g∘f（HTT の (2) と一致）。結論：f は余極限を保存する左随伴として、g は右随伴として accessible で、その同じ合成 L も accessible（(2)⇒(3) に一致）。L の accessibility だけから像の accessibility を得る逆方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible
attribute [cite HTT "5.5.2.10" (partial := stronger-hyp) "仮定：presentable な始域と accessible な標的 D（Lean が強い：原典の局所小性だけより強いが、D の presentability は不要）。結論：元の F が右随伴を持つことと全小余極限保存の iff（この場合に一致）。必要な始域上の全連続前層の表現定理は presentableContinuous_isRepresentable で供給でき、未証明の比較仮定ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native
attribute [cite HTT "5.5.2.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits
