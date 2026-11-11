module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.AdjunctionHomLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.PostcompLimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：strict な錐の通常の関手による像を coherent nerve の後合成と厳密に照合する。
方針：順序図式の豊穣な表示の自然性を図式と join の全標準単体へ適用する。
規約：両圏は対象と Hom の宇宙を共有し、局所 Kan 性は等式の構成には不要。
使われ方：HTT 4.2.4.1・5.2.4.6、右随伴の像の錐を実際の ∞ 関手の像として公開する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 概要：通常の nerve の coherent 表示は豊穣関手による後合成と可換。
方針：各順序図式の定値な豊穣 Hom の後合成の式を使う。
規約：通常の作用は coherentEnrichedUnderlyingFunctor を使う。
使われ方：Kerodon 2.4.3（Tag 00KM）、通常の図式の像と実際の ∞ 関手の同定。 -/
lemma nerveToCoherent_postcomp (R : EnrichedFunctor SSet.{u} D C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _).comp SSet R = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp]
  rfl

variable {I : Type u} [SmallCategory I]

/-- 概要：strict な図式の右像の coherent 表示は元の表示への実際の後合成。
方針：各単体を通常の順序図式として表し、豊穣関手の後合成の式を使う。
規約：添字の持ち上げを厳密に保持する。
使われ方：HTT 4.2.4.1、右随伴の ∞ 関手による図式の像の固定条件。 -/
lemma strictCoherentDiagram_postcomp (F : I ⥤ D) (R : EnrichedFunctor SSet.{u} D C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _).comp SSet R = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp]
  rfl

omit [SimplicialCategory C] [SimplicialCategory D] in
/-- 概要：射列に一射を前置する操作は通常の関手による後合成と可換。
方針：前置した射、零番の対象、残りの射列を比較する。
規約：射列の長さは零を含む任意の自然数。
使われ方：元の錐の脚を前置した単体を右随伴で写す計算。 -/
lemma composableArrows_precomp_postcomp {n : ℕ} (A : ComposableArrows D n)
    {d : D} (f : d ⟶ A.obj 0) (G : D ⥤ C) :
    ComposableArrows.precomp A f ⋙ G = ComposableArrows.precomp (A ⋙ G) (G.map f) := by
  refine ComposableArrows.ext_succ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：strict な錐の像の join の射は元の射の coherent nerve への後合成。
方針：頂点と右因子の全標準単体で錐の射列の後合成を比較する。
規約：錐の極限性や図式の strict 化を仮定しない。
使われ方：HTT 4.2.4.1・5.2.4.6、像の錐の実際の全高次データの同定。 -/
lemma strictCoherentConeMap_postcomp {F : I ⥤ D} (c : Cone F)
    (R : EnrichedFunctor SSet.{u} D C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).mapCone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_right_hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap_inl]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex R c.pt
  · intro n a
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap_simplex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap_simplex,
      Category.assoc, SSet.yonedaEquiv_symm_comp]
    congr 2
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _).comp SSet R = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp]
    congr 1
    change (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 2)) →o Fin (n + 2)).toFunctor ⋙
      (ComposableArrows.precomp ((SSet.yonedaEquiv a).down ⋙ F)
        (c.π.app ((SSet.yonedaEquiv a).down.obj 0)) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) = _
    rw [composableArrows_precomp_postcomp]
    rfl

/-- 概要：strict な錐の右像は元の native な錐の後合成を図式の等式で移送したもの。
方針：join の射の厳密な等式を固定図式の部分型へ移す。
規約：実際の ∞ 関手 coherentNerveMap R の像と同定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、Hom 同型による極限保存を ∞ 関手の言葉で述べる。 -/
lemma strictCoherentCone_postcomp {F : I ⥤ D} (c : Cone F)
    (R : EnrichedFunctor SSet.{u} D C) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)).cast
        (strictCoherentDiagram_postcomp F R) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).mapCone c) := by
  apply Subtype.ext
  exact strictCoherentConeMap_postcomp c R

/-- 概要：Hom 随伴同型を持つ豊穣右関手の coherent nerve は strict な表示の極限錐を保つ。
方針：通常の右随伴の像の錐の極限性を、元の native な錐の実際の後合成へ戻す。
規約：任意の小圏の図式で、結論の錐の全高次データは coherentNerveMap R による像。
使われ方：HTT 4.2.4.1・5.2.4.6、E2b の右導来忘却関手の極限保存の接続先。 -/
lemma strictCoherentCone_postcomp_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
    {adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SimplicialAdjunctionHomIso adj)
    {F : I ⥤ D} (c : Cone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_map_isLimit_of_adjunctionHomIso e c hc
  rw [← strictCoherentCone_postcomp c R] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).mp h

/-- 概要：Hom 随伴同型を持つ豊穣右関手は strict な表示を持つ図式の全極限錐を保つ。
方針：一つの標準錐の保存を証明し、同じ図式上の任意の極限錐との同型で輸送する。
規約：d は任意の coherent な錐で、strict な通常の錐であることは仮定しない。
使われ方：HTT 4.2.4.1・5.2.4.6、𝒮・Sp の具体的な極限錐から全極限錐への適用。 -/
lemma strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
    {adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SimplicialAdjunctionHomIso adj)
    {F : I ⥤ D} (c : Cone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (d.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_postcomp_of_one_limitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) hc
    (strictCoherentCone_postcomp_isLimit_of_adjunctionHomIso R e c hc) d hd

end
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
