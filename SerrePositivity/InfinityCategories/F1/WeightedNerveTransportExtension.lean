module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveTransportComparison
public import SerrePositivity.InfinityCategories.F1.StrictDiagramExtensionSpace

/-!
概要：weighted nerve の標準単位を厳密に固定した strict な比較の延長。
方針：恒等射評価で単位の単射性を検出し、既存の制限の全境界持ち上げを適用する。
規約：係数図式の変更に沿う延長であり、底の部分単体集合からの表現の延長とは区別する。
使われ方：Kerodon §§5.6.5–5.6.8、標準比較を保つ高次の選択空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：weighted nerve の標準単位は各成分で単射。
方針：恒等射評価との合成が fiber の標準同型になることを使う。
規約：係数図式の Kan 性は不要。
使われ方：Kerodon §5.6.5、標準単位に沿う制限の持ち上げ性。 -/
instance weightedNerveTransportUnit_app_mono {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : Mono ((weightedNerveTransportUnit F).app c) :=
  mono_of_mono_fac (weightedNerveTransportUnit_evaluate F c)

/-- 概要：標準単位を越える strict transport への制限は全境界を持ち上げる。
方針：単位の成分の単射性と同値性を strict な制限の判定へ適用する。
規約：標的は任意の left fibration q の strict transport。
使われ方：Kerodon §§5.6.5–5.6.8、指定された比較と高次パラメーターを固定した延長。 -/
lemma weightedNerveTransportUnit_restriction_trivialKanFibration
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    [∀ c, KanComplex (F.obj c)] {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    TrivialKanFibration (strictDiagramMappingPre (weightedNerveTransportUnit F)
      (leftStrictTransportDiagram q)) := by
  exact strictDiagramMappingPre_trivialKanFibration (weightedNerveTransportUnit F)
    (weightedNerveTransportUnit_isQCatEquivalence F) q

/-- 概要：標準単位を越えて比較 θ を厳密に延長する空間は可縮な Kan 複体。
方針：単位に沿う制限の全境界持ち上げを、その θ 上の fiber に移す。
規約：θ は図式全体の自然変換として固定する。
使われ方：Kerodon §5.6.5、標準単位に沿う延長の存在と高次の一意性。 -/
lemma weightedNerveTransportUnit_extensionSpace_isContractibleKan
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    [∀ c, KanComplex (F.obj c)] {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] (θ : F ⟶ leftStrictTransportDiagram q) :
    IsContractibleKan (strictDiagramExtensionSpace (weightedNerveTransportUnit F) q θ) := by
  have := weightedNerveTransportUnit_restriction_trivialKanFibration F q
  exact vertexFiber_isContractibleKan _ _

/-- 概要：strict transport に対する標準単位は図式全体で同値な厳密な左逆を持つ。
方針：恒等変換を標準単位に沿って延長し、各成分の二対三則を使う。
規約：左逆の自然性と単位との合成の等式を同時に保つ。
使われ方：Kerodon Corollary 5.6.0.6、strict な像での単位の回収。 -/
lemma exists_weightedNerveTransportUnit_retraction
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    ∃ r : leftStrictTransportDiagram
        (weightedNerveProjection (leftStrictTransportDiagram q)) ⟶ leftStrictTransportDiagram q,
      weightedNerveTransportUnit (leftStrictTransportDiagram q) ≫ r =
        𝟙 (leftStrictTransportDiagram q) ∧ ∀ c, IsQCatEquivalence (r.app c) := by
  obtain ⟨r, hr⟩ := exists_strictDiagramExtension
    (weightedNerveTransportUnit (leftStrictTransportDiagram q))
    (weightedNerveTransportUnit_isQCatEquivalence (leftStrictTransportDiagram q)) q (𝟙 _)
  refine ⟨r, hr, ?_⟩
  intro c
  apply (weightedNerveTransportUnit_isQCatEquivalence (leftStrictTransportDiagram q) c).cancel_left
  have h := congrArg (fun t ↦ t.app c) hr
  change (weightedNerveTransportUnit (leftStrictTransportDiagram q)).app c ≫ r.app c = 𝟙 _ at h
  rw [h]
  exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

end SerrePositivity.InfinityCategories
