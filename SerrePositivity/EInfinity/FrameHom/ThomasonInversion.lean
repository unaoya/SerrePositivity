module

public import SerrePositivity.EInfinity.FrameHom.GrothendieckCommaRetraction
public import SerrePositivity.EInfinity.FrameHom.GrothendieckCommaComparison
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 元の Thomason 比較射の反転性

概要：同じ宇宙の小圏の Cat 値図式で、元の Thomason 射を局所化で反転する。
方針：comma 図式の射影・移送の成分不変性・元の自然性の正方形を合成する。
規約：単体集合モデル・fiber の Kan 性・比較の弱同値性は入力しない。
使われ方：元の固定右脚から三本矢の全図式の nerve への比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.Thomason
open SerrePositivity.SimplicialModel

variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

/-- 元の Cat 値図式の Thomason 比較射そのものは局所化で可逆。 -/
lemma map_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (map G)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let β := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportComparison G
  have : IsIso (Q.map ((BarConstruction.functor D).map (nerveComparison β))) :=
    BarRows.map_localized_isIso _ (transport_localized_isIso G)
  have hf := commaMap_forget_localized_isIso G
  have hh := AnodyneHomotopy.map_homotopy_eq Q
    (Localization.inverts _ SSet.anodyneExtensions)
    (NerveHomotopy.homotopy (commaTotalTransport G))
  have hc : IsIso (Q.map (map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) ≫ nerveMap (Grothendieck.map β))) := by
    rw [Q.map_comp, ← hh, ← Q.map_comp]
    exact hf
  have hn : IsIso (Q.map ((BarConstruction.functor D).map (nerveComparison β) ≫ map G)) := by
    rw [← map_naturality β]
    exact hc
  rw [Q.map_comp] at hn
  exact (isIso_comp_left_iff _ _).mp hn

/-- 同じ元の比較射は、F1b の弱ホモトピー同値のクラスにも属する。 -/
lemma map_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (map G) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _ (map_localized_isIso G)

end SerrePositivity.EInfinity.FrameHom.Thomason
