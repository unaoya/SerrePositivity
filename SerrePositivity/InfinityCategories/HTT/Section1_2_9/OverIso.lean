module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OverOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：通常の Over の nerve と元の頂点上の native な slice を同型にする。
方針：Under の比較を反転し標的と零単体の固定図式を正規化する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory Limits _root_.SSet _root_.Opposite
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HTT.Section1_2_9

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Over の nerve を反転した点図式上の slice へ写す同型。
方針：Under の nerve の比較と native な coslice の反転を合成する。
規約：反転した標的と点図式をまだ保持する。
使われ方：元の頂点上の slice の同型への中間表示。 -/
def nerveOverRawSliceIso : nerve (Over c) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverOppositeUnderIso c ≪≫ SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderIso (op c)) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))

/-- 概要：Over の nerve と元の頂点上の native な slice の同型。
方針：標的と点図式を同型で戻し最後の等式で輸送する。
規約：元の指定された頂点 c を固定する。
使われ方：左 Kan の局所添字の古典比較。 -/
def nerveOverIso : nerve (Over c) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) := by
  let p := SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))
  let q := (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_isIso p q
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv
  exact _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c ≪≫ asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q) ≪≫
    asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv) ≪≫
      eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverBase_eq c))

/-- 概要：中間の slice の同型は標的を戻すと元の忘却射影を与える。
方針：coslice の反転の射影の式と Under の比較を使う。
規約：標的を戻す同型を明記する。
使われ方：最終的な射影の保存の証明。 -/
lemma nerveOverRawSliceIso_projection : (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso c).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom = nerveMap (Over.forget c) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso]
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso _).hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso_projection]
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverOppositeUnderIso c).hom ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap (op c)) ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c))) ≫ _ = _
  rw [← Category.assoc (SSet.opFunctor.map _), ← SSet.opFunctor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap_projection]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverOppositeUnderIso_projection c

/-- 概要：Over の nerve と slice の同型は元の忘却射影を厳密に保つ。
方針：反転・制限・後合成の射影の式を順に使う。
規約：単体集合の射の厳密な等式。
使われ方：左 Kan の局所図式の一致。 -/
lemma nerveOverIso_projection : (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) =
    nerveMap (Over.forget c) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverBase_eq c)]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverRestrict_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]
  rw [← Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverRawSliceIso_projection c

end SerrePositivity.InfinityCategories.HTT.Section1_2_9

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.9.1" (partial := special) "仮定：普通圏 C の nerve と c に限定（Lean が強い特殊形）。結論：nerve(Over c) と準圏 sliceOver(nervePoint c) の実際の同型を得るので、naive overcategory が正しい slice を与えるという原典の存在する場合の明示例に一致。一般の topological/enriched C の naive approximation の基準は含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
attribute [cite HTT "1.2.9.6"] _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
attribute [cite HTT "5.2.5.1" (partial := special) "仮定：引き戻しを持つ通常圏 C の随伴 F⊣G、対象 c（Lean が強い：通常圏の神経の場合）。結論：Over.post F の右随伴は Over.post G と単位 c→GFc に沿う pullback の合成（この場合に (1)(2) が一致）。通常の Over の nerve と native な頂点上 slice の同型、および通常随伴を元の nerve 間の ∞ 随伴へ移す宣言を併用する。一般の準圏の slice 随伴は含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
attribute [cite HTT "5.2.5.2" (partial := special) "仮定：引き戻しを持つ通常圏間の随伴 F⊣G と F(c)→d（Lean が強い：C,D は神経、形状 K は一点）。結論：C/c→D/d の F による後合成と指定射による後合成の合成が右随伴を持つ（この場合に (1) と一致）。二つの明示随伴の合成で得られる。任意の K に対する主張、および (2) の単一の図式 pullback による計算との比較は含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
