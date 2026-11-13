module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SpaceArbitraryPushouts

/-!
概要：共通部分の余極限から二つの部分余錐の頂点への実際の Kan 値 span と、その押し出しを構成する。
方針：部分余極限の付加による比較辺を通常の Kan 対象の射へ戻し、既存の一般の span の余極限へ渡す。
規約：span 自体の余極限を構成する。元の貼り合わせた coherent 図式の余極限性は別途検証する。
使われ方：一般の coherent 図式のセル付加で、部分余極限対象から新しい頂点を組み立てる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)

/-- 共通部分の余極限頂点から、二つの部分余錐の頂点への実際の Kan 値 span。 -/
def partialColimitApexSpan : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  AsSmall.down ⋙ span (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom c hc i F hi dB)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexHom c hc j G hj dC)

/-- 部分余極限対象の実際の span の押し出しを、新しい頂点候補とする。 -/
def partialColimitPushoutObject : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceArbitraryPushoutObject (partialColimitApexSpan c hc i F hi dB j G hj dC)

/-- 部分余極限対象の span 上の実際の coherent な余極限余錐。 -/
def partialColimitPushoutCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (partialColimitApexSpan c hc i F hi dB j G hj dC)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceArbitraryPushoutCocone (partialColimitApexSpan c hc i F hi dB j G hj dC)

/-- span の余錐の頂点は、構成した小さい Kan 対象の標準頂点。 -/
lemma partialColimitPushoutCocone_vertex :
    (partialColimitPushoutCocone c hc i F hi dB j G hj dC).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (partialColimitPushoutObject c hc i F hi dB j G hj dC) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceArbitraryPushoutCocone_vertex _

/-- 部分余極限対象の span 上では、構成した余錐は実際の ∞ 余極限余錐。 -/
lemma partialColimitPushoutCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (partialColimitPushoutCocone c hc i F hi dB j G hj dC) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.spaceArbitraryPushoutCocone_isColimitCone _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
