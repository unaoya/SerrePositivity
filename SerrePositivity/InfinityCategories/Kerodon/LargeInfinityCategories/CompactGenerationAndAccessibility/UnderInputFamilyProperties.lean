module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.UnderInputFamilies

/-!
概要：指定成分始点を含む入力族の小ささ、compact 性、全制限の等式を証明する。
方針：join の小ささと元の全入力の厳密な制限公式を二点族へまとめる。
規約：元の成分型と標的を保持する。
使われ方：両成分射影の under 試験の実際の交互構成への入力。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：第一指定始点付き入力形状は二成分とも quasicategory。
方針：元の join の quasicategory 性を二点族へまとめる。
規約：小さい元の形状を保つ。
使われ方：相対交互構成の入力形状。 -/
lemma firstUnderInputShapes_quasicategory (A K : SSet.{u})
    [Quasicategory A] [Quasicategory K] : ∀ c, Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (show Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) from inferInstance)
    (show Quasicategory (K) from inferInstance)

/-- 概要：第一指定始点付き入力形状は同じ濃度で小さい。
方針：元の二つの小形状の join の小ささを使う。
規約：濃度を上げず、元の小宇宙に保つ。
使われ方：追加入力付き compact 表示の構成。 -/
lemma firstUnderInputShapes_isKappaSmall {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {A K : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join Fact.out hA hK) hK

/-- 概要：第一指定始点付き入力族の第一入力包含は単射。
方針：元の join 右包含または恒等射の単射性を使う。
規約：第一脚の同値持ち上げに必要な包含を保つ。
使われ方：追加入力を保持する厳密化。 -/
instance firstUnderInputInclusions_first_mono (A K : SSet.{u}) :
    Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputInclusions A K) 0) := by
  change Mono ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.mono_uliftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)

/-- 概要：第二指定始点付き入力形状は二成分とも quasicategory。
方針：元の join の quasicategory 性を二点族へまとめる。
規約：小さい元の形状を保つ。
使われ方：相対交互構成の入力形状。 -/
lemma secondUnderInputShapes_quasicategory (A K : SSet.{u})
    [Quasicategory A] [Quasicategory K] : ∀ c, Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ (show Quasicategory (K) from inferInstance)
    (show Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) from inferInstance)

/-- 概要：第二指定始点付き入力形状は同じ濃度で小さい。
方針：元の二つの小形状の join の小ささを使う。
規約：濃度を上げず、元の小宇宙に保つ。
使われ方：追加入力付き compact 表示の構成。 -/
lemma secondUnderInputShapes_isKappaSmall {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {A K : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputShapes A K c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join Fact.out hA hK)

/-- 概要：第二指定始点付き入力族の第一入力包含は単射。
方針：元の join 右包含または恒等射の単射性を使う。
規約：第一脚の同値持ち上げに必要な包含を保つ。
使われ方：追加入力を保持する厳密化。 -/
instance secondUnderInputInclusions_first_mono (A K : SSet.{u}) :
    Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputInclusions A K) 0) := by
  change Mono ((𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj K)))
  infer_instance

variable {A K : SSet.{u}} {B : SSet.{u + 1}} [Quasicategory B]
  {C : Fin 2 → SSet.{u + 1}} [∀ c, Quasicategory (C c)]
  (μ : Cardinal.{u}) (p : ∀ c, C c ⟶ B)
  (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback (p 0) (p 1))
  (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)

/-- 概要：第一指定始点を含む追加入力の全頂点は元の各成分で compact。
方針：指定成分は compact 始域 slice の頂点条件、他成分は元の入力条件を使う。
規約：元の対象圏の compact 性を保つ。
使われ方：accessible 性からの実際の compact 正規化表示。 -/
lemma firstUnderInputDiagrams_compact
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ (p 0) (p 1)
      ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v)) :
    ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams μ p x U t c).app (Opposite.op ⦋0⦌) v) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput_compact μ (x ≫ pullback.fst (p 0) (p 1)) t
  · exact fun v ↦ (hU v).2

/-- 概要：第一指定始点付き入力族の元の入力を厳密に回収する。
方針：指定成分の全制限公式と他成分の恒等制限をまとめる。
規約：元の可変入力と固定標的の全単体を保持する。
使われ方：相対交互構成の共通入力の固定条件。 -/
lemma firstUnderInputDiagrams_fixed
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ pullback.fst (p 0) (p 1)) =
        U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst (p 0) (p 1))) :
    ∀ c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputInclusions A K c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputDiagrams μ p x U t c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInput p (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput_right_of_companion μ x (pullback.fst (p 0) (p 1)) t U hU
  · exact Category.id_comp _

/-- 概要：第一指定始点付き入力族の元の全増大余錐を厳密に回収する。
方針：指定成分の全制限公式と他成分の恒等制限をまとめる。
規約：元の可変入力と固定標的の全単体を保持する。
使われ方：相対交互構成の共通入力の固定条件。 -/
lemma firstUnderInputDiagrams_cocone_fixed
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.fst (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ pullback.fst (p 0) (p 1)) =
        U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.fst (p 0) (p 1))) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputInclusions A K c) (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.firstUnderInputCocones μ p x U t c).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInputCocone p (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U) c).val := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInputCocone_right_of_companion μ x (pullback.fst (p 0) (p 1)) t U hU
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (𝟙 _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
    rfl

/-- 概要：第二指定始点を含む追加入力の全頂点は元の各成分で compact。
方針：指定成分は compact 始域 slice の頂点条件、他成分は元の入力条件を使う。
規約：元の対象圏の compact 性を保つ。
使われ方：accessible 性からの実際の compact 正規化表示。 -/
lemma secondUnderInputDiagrams_compact
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.snd (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ (p 0) (p 1)
      ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) v)) :
    ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputDiagrams μ p x U t c).app (Opposite.op ⦋0⦌) v) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · exact fun v ↦ (hU v).1
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput_compact μ (x ≫ pullback.snd (p 0) (p 1)) t

/-- 概要：第二指定始点付き入力族の元の入力を厳密に回収する。
方針：指定成分の全制限公式と他成分の恒等制限をまとめる。
規約：元の可変入力と固定標的の全単体を保持する。
使われ方：相対交互構成の共通入力の固定条件。 -/
lemma secondUnderInputDiagrams_fixed
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.snd (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ pullback.snd (p 0) (p 1)) =
        U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.snd (p 0) (p 1))) :
    ∀ c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputInclusions A K c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputDiagrams μ p x U t c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInput p (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · exact Category.id_comp _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInput_right_of_companion μ x (pullback.snd (p 0) (p 1)) t U hU

/-- 概要：第二指定始点付き入力族の元の全増大余錐を厳密に回収する。
方針：指定成分の全制限公式と他成分の恒等制限をまとめる。
規約：元の可変入力と固定標的の全単体を保持する。
使われ方：相対交互構成の共通入力の固定条件。 -/
lemma secondUnderInputDiagrams_cocone_fixed
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ pullback.snd (p 0) (p 1))}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactSourceSliceInclusion μ (x ≫ pullback.snd (p 0) (p 1)) =
        U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x (pullback.snd (p 0) (p 1))) :
    ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputInclusions A K c) (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.secondUnderInputCocones μ p x U t c).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInputCocone p (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U) c).val := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ ?_ ?_
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (𝟙 _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
    rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.extendedSourceSliceInputCocone_right_of_companion μ x (pullback.snd (p 0) (p 1)) t U hU

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
