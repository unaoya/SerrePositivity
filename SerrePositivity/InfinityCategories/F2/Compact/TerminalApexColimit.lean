module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFilteredTerminal
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：一般 coherent filtered 図式の各値と指定余錐頂点が終対象なら、その余錐は余極限。
方針：元の標準余極限の終対象性を使い、元の比較辺の射影の可逆性を反映する。
規約：指定余錐の全体を保持。使われ方：始対象からの Hom の余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の各値と元の指定頂点が終対象なら、同じ filtered 余錐自体が余極限。 -/
lemma isColimitCone_of_terminal_values {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hf : ∀ b : B _⦋0⦌, IsTerminalVertex (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
    (c : JoinCocone F) (hc : IsTerminalVertex c.vertex) : IsColimitCone c := by
  let d := coherentDiagramTotalCocone F
  have hd : IsColimitCone d := coherentDiagramTotalCocone_isColimit F
  have ht : IsTerminalVertex d.vertex := by
    rw [show d.vertex = coherentDiagramTotalVertex F from coherentDiagramTotalCocone_vertex F]
    exact coherentFilteredTotalVertex_isTerminal F hf
  obtain ⟨e⟩ := IsInitialVertex.nonempty_edge (X := sliceUnder F) hd c
  have hp : IsInvertibleEdge (e.map ((truncation 2).map (sliceUnderProjection F))) :=
    isIso_of_isTerminal ht.isTerminalHo hc.isTerminalHo _
  have he := leftFibration_reflects_invertibleEdge (sliceUnderProjection F) e hp
  have : IsIso (SSet.HomotopyCategory.homMk (SSet.Edge.ofTruncated (X := sliceUnder F) e)) := he
  exact IsInitialVertex.of_vertexIso hd (asIso (SSet.HomotopyCategory.homMk
    (SSet.Edge.ofTruncated (X := sliceUnder F) e)))

end SerrePositivity.InfinityCategories.F2.Compact
