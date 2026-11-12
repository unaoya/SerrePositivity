module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanSequenceMonoReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SpaceSequentialColimits

/-!
概要：一般の遷移を持つ Kan 複体列の実際の homotopy 逐次余極限を元の図式上に構成する。
方針：全隣接射が単射な列に置換し、その逐次余極限を成分ごとの同値に沿って輸送する。
規約：元の遷移に単射性を仮定せず、置換した列の通常の余極限を頂点として保持する。
使われ方：HTT 4.2.4.1、F2 の 𝒮 の逐次余極限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：任意の Kan 複体列の単射な置換の通常の逐次余極限を持つ Kan 対象。
方針：全隣接射が単射な置換に対して既存の実際の逐次余極限対象を取る。
規約：元の列の通常の余極限と同一とは主張しない。
使われ方：HTT 4.2.4.1、一般の列の homotopy 逐次余極限対象。 -/
def spaceArbitrarySequentialColimitObject (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanSequentialColimitObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSequenceMonoReplacement F)

/-- 概要：任意の Kan 複体列の元の coherent 表示上の実際の余極限余錐。
方針：単射な置換の余極限余錐を元の図式への成分ごとの同値な比較で輸送する。
規約：元の全隣接遷移に条件を付けない。
使われ方：HTT 4.2.4.1、F2 の 𝒮 の任意の逐次余極限。 -/
def spaceArbitrarySequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSequenceMonoComparison F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSequenceMonoComparison_isQCatEquivalence F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceSequentialColimitCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSequenceMonoReplacement F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceSequentialColimitCocone_isColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSequenceMonoReplacement F))

/-- 概要：輸送した元の列の余錐の頂点は置換列の逐次余極限の標準頂点に厳密に一致する。
方針：成分ごとの同値に沿う輸送の頂点と既存の逐次余極限の頂点を計算する。
規約：対象の同値だけではなく頂点の等号。
使われ方：実際の homotopy 逐次余極限対象と native な余錐の照合。 -/
lemma spaceArbitrarySequentialColimitCocone_vertex (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceArbitrarySequentialColimitCocone F).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (spaceArbitrarySequentialColimitObject F) := by
  rw [spaceArbitrarySequentialColimitCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceSequentialColimitCocone_vertex]
  rfl

/-- 概要：一般の遷移を持つ Kan 複体列の構成した余錐は native な ∞ 余極限。
方針：単射な置換での余極限性を図式全体の同型に沿って輸送する。
規約：単射性、追加の Hom 条件、比較同値を仮定しない。
使われ方：HTT 4.2.4.1、𝒮 の homotopy 逐次余極限と ∞ 逐次余極限の比較。 -/
lemma spaceArbitrarySequentialColimitCocone_isColimitCone
    (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (spaceArbitrarySequentialColimitCocone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanDiagramColimitTransport_isColimit _ _ _ _

/-- 概要：任意の strict な Kan 複体列の空間値図式は ∞ 余極限を持つ。
方針：構成した実際の余極限余錐と普遍性を存在の証拠に使う。
規約：元の F1 の標準図式そのものについて述べる。
使われ方：F2 に公開する 𝒮 の逐次余極限の存在の共有界面。 -/
lemma spaceInfinity_hasColimit_sequence (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  ⟨spaceArbitrarySequentialColimitCocone F,
    spaceArbitrarySequentialColimitCocone_isColimitCone F⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
