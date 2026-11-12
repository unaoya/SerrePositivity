module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.KanMonoArrowFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：任意の Kan 複体の span の homotopy 押し出しを元の空間値図式上に構成する。
方針：左脚の境界分解で単射な span を作り、成分ごとの同値で元の図式へ余極限余錐を輸送する。
規約：元の両脚の単射性を仮定せず、構成した余極限対象を頂点の等号で保持する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、F2 の任意の span の homotopy 押し出し。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：任意の Kan 値 span の左脚を単射に替えた Kan 値 span。
方針：左脚を Kan な中間対象への単射に替え、中心と右端と右脚を保持する。
規約：元の左端への比較は境界分解の右因子。
使われ方：一脚が単射な homotopy 押し出しの構成への入力。 -/
def kanSpanMonoReplacement (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  AsSmall.down ⋙ span (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowLeft (F.map (AsSmall.up.map WalkingSpan.Hom.fst)))
    (F.map (AsSmall.up.map WalkingSpan.Hom.snd))

/-- 概要：単射に替えた span から元の span への実際の自然変換。
方針：中心と右端では恒等、左端では境界分解の右因子を使う。
規約：台の単体集合の図式の厳密な自然性を要求する。
使われ方：coherent な図式の同型への成分ごとの比較。 -/
def kanSpanMonoReplacementComparison (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    kanSpanMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget where
  app i := by
    rcases i with ⟨i⟩
    cases i with
    | none => exact 𝟙 _
    | some k =>
      cases k with
      | left =>
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowRight (F.map (AsSmall.up.map WalkingSpan.Hom.fst)))
      | right => exact 𝟙 _
  naturality i j f := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases f with ⟨f⟩
    change WidePushoutShape.Hom i j at f
    cases f with
    | id i =>
      change (kanSpanMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map (𝟙 _) ≫ _ =
        _ ≫ (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map (𝟙 _)
      rw [(kanSpanMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map_id,
        (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map_id, Category.id_comp, Category.comp_id]
    | init k =>
      cases k with
      | left =>
        change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowLeft _) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowRight _) = 𝟙 _ ≫ _
        rw [Category.id_comp, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrow_fac]
        rfl
      | right =>
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        simp only [Category.comp_id, Category.id_comp]
        rfl

/-- 概要：置換した span の左脚は台で単射。
方針：境界分解の左因子の単射性を使う。
規約：元の span に条件を付けない。
使われ方：実際の一脚単射の homotopy 押し出し定理の仮定の検証。 -/
instance kanSpanMonoReplacement_left_mono (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    Mono ((kanSpanMonoReplacement F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (AsSmall.up.map WalkingSpan.Hom.fst)) := by
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowLeft (F.map (AsSmall.up.map WalkingSpan.Hom.fst))))
  infer_instance

/-- 概要：置換した span から元の span への比較は全成分で同値。
方針：中心と右端の恒等射、左端の trivial Kan fibration の同値性を使う。
規約：元の両脚の単射性は不要。
使われ方：F1 の点ごとの判定により図式全体の同型を得る。 -/
lemma kanSpanMonoReplacementComparison_isQCatEquivalence
    (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (i : AsSmall.{u} WalkingSpan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := ((kanSpanMonoReplacement F).obj i).obj) (Y := (F.obj i).obj)
      ((kanSpanMonoReplacementComparison F).app i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  | some k =>
    cases k with
    | left =>
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
        (X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowObject (F.map (AsSmall.up.map WalkingSpan.Hom.fst))).obj)
        (Y := (F.obj (AsSmall.up.obj WalkingSpan.left)).obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.kanMonoArrowRight_homotopyEquivalence _)
    | right => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

/-- 概要：任意の Kan 値 span の単射な置換の押し出しを Kan 置換した実際の対象。
方針：左脚を境界分解した後で既存の homotopy 押し出し対象を使う。
規約：元の図式上へ戻した余錐でも同じ頂点を保持する。
使われ方：HTT 4.2.4.1、𝒮 の任意の span の homotopy 押し出し対象。 -/
def spaceArbitraryPushoutObject (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.kanHomotopyPushoutObject (kanSpanMonoReplacement F)

/-- 概要：任意の Kan 値 span の元の coherent な図式上の実際の余極限余錐。
方針：単射な置換の余極限余錐を成分ごとの同値な比較に沿って輸送する。
規約：元の図式 F の射を変更せず、余錐は coherent な余錐として戻す。
使われ方：HTT 4.2.4.1、F2 の単射性を仮定しない homotopy 押し出し。 -/
def spaceArbitraryPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport (kanSpanMonoReplacementComparison F)
    (kanSpanMonoReplacementComparison_isQCatEquivalence F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.spaceHomotopyPushoutCocone (kanSpanMonoReplacement F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.spaceHomotopyPushoutCocone_isColimitCone (kanSpanMonoReplacement F))

/-- 概要：元の span 上に戻した余錐の頂点は構成した homotopy 押し出し対象の標準頂点。
方針：頂点を保持した輸送と一脚単射の押し出しの頂点の式を使う。
規約：単なる同値でなく頂点の等号。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、任意の span の実際の余極限対象の同定。 -/
lemma spaceArbitraryPushoutCocone_vertex (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceArbitraryPushoutCocone F).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (spaceArbitraryPushoutObject F) := by
  rw [spaceArbitraryPushoutCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.spaceHomotopyPushoutCocone_vertex]
  rfl

/-- 概要：任意の Kan 値 span は元の空間値図式上で実際の ∞ 押し出し余錐を持つ。
方針：単射な置換での余極限性を図式全体の同型に沿って輸送する。
規約：脚の単射性、追加の Hom 条件、比較同値を仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、F2 の 𝒮 の homotopy 押し出し。 -/
lemma spaceArbitraryPushoutCocone_isColimitCone
    (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (spaceArbitraryPushoutCocone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport_isColimit _ _ _ _

/-- 概要：任意の strict な Kan 値 span の coherent 表示は余極限を持つ。
方針：構成した実際の余極限余錐を存在の証拠に使う。
規約：元の F1 の空間値図式に対する存在。
使われ方：F2 の 𝒮 の押し出しの存在の共有界面。 -/
lemma spaceInfinity_hasColimit_span (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  ⟨spaceArbitraryPushoutCocone F, spaceArbitraryPushoutCocone_isColimitCone F⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
