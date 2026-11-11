module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramExtensionSpace

/-!
概要：weighted nerve の標準単位を厳密に固定した strict な比較の延長。
方針：恒等射評価で単位の単射性を検出し、既存の制限の全境界持ち上げを適用する。
規約：係数図式の変更に沿う延長であり、底の部分単体集合からの表現の延長とは区別する。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、標準比較を保つ高次の選択空間。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：weighted nerve の標準単位は各成分で単射。
方針：恒等射評価との合成が fiber の標準同型になることを使う。
規約：係数図式の Kan 性は不要。
使われ方：Kerodon §5.6.5（Tag 028U）、標準単位に沿う制限の持ち上げ性。 -/
instance weightedNerveTransportUnit_app_mono {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).app c) :=
  mono_of_mono_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_evaluate F c)

/-- 概要：標準単位を越える strict transport への制限は全境界を持ち上げる。
方針：単位の成分の単射性と同値性を strict な制限の判定へ適用する。
規約：標的は任意の left fibration q の strict transport。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、指定された比較と高次パラメーターを固定した延長。 -/
lemma weightedNerveTransportUnit_restriction_trivialKanFibration
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    [∀ c, KanComplex (F.obj c)] {E : SSet.{u}}
    (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_isQCatEquivalence F) q

/-- 概要：標準単位を越えて比較 θ を厳密に延長する空間は可縮な Kan 複体。
方針：単位に沿う制限の全境界持ち上げを、その θ 上の fiber に移す。
規約：θ は図式全体の自然変換として固定する。
使われ方：Kerodon §5.6.5（Tag 028U）、標準単位に沿う延長の存在と高次の一意性。 -/
lemma weightedNerveTransportUnit_extensionSpace_isContractibleKan
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    [∀ c, KanComplex (F.obj c)] {E : SSet.{u}}
    (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramExtensionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F) q θ) := by
  have := weightedNerveTransportUnit_restriction_trivialKanFibration F q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：strict transport に対する標準単位は図式全体で同値な厳密な左逆を持つ。
方針：恒等変換を標準単位に沿って延長し、各成分の二対三則を使う。
規約：左逆の自然性と単位との合成の等式を同時に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な像での単位の回収。 -/
lemma exists_weightedNerveTransportUnit_retraction
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≫ r =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ∧ ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (r.app c) := by
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_strictDiagramExtension
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) q (𝟙 _)
  refine ⟨r, hr, ?_⟩
  intro c
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) c).cancel_left
  have h := congrArg (fun t ↦ t.app c) hr
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)).app c ≫ r.app c = 𝟙 _ at h
  rw [h]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
