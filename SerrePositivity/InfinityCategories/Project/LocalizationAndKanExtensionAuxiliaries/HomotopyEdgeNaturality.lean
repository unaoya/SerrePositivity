module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：指定した単体的ホモトピーの各辺での自然性。
方針：ホモトピー圏の自然変換の成分を実際の垂直辺と同定する。
規約：始域・標的の quasicategory 性は不要。
使われ方：Cat_∞ の引き戻し錐の各脚の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries

/-- 概要：指定された両端点を持つ自然変換の成分は元の垂直辺の類。
方針：端点の等式で戻し、自然変換と頂点辺の定義を比較する。
規約：辺の代表を変更しない。
使われ方：全錐の比較ホモトピーの成分を計算する。 -/
lemma homotopyNatTransOfEndpoints_app {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (SSet.HomotopyCategory.mk x) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  rcases H with ⟨h, h₀, h₁, rel⟩
  change SSet.ι₀ ≫ h = f at h₀
  change SSet.ι₁ ≫ h = g at h₁
  subst f
  subst g
  rfl
/-- 概要：指定ホモトピーの四角形は各辺でホモトピー圏内で可換。
方針：両端の関手の間の自然変換の自然性を適用する。
規約：元の辺と両端の垂直辺を明示する。
使われ方：二脚と図式の切断の辺の合成の比較。 -/
lemma homotopy_edge_naturality {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f)) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map g)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).naturality
    (SSet.Truncated.HomotopyCategory.homMk e)
  change SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (SSet.HomotopyCategory.mk y) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (SSet.HomotopyCategory.mk x) ≫
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map g)) at h
  rw [homotopyNatTransOfEndpoints_app, homotopyNatTransOfEndpoints_app] at h
  exact h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
