module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyFatCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-!
概要：定値図式へのホモトピーを、同じ図式・頂点の native な余錐として実現する。
方針：fat join の両端固定比較で回収し、元の全図式との相対ホモトピーを保持する。
規約：極限性・余極限性はこの実現だけからは主張しない。
使われ方：全空間の単位を表す変換を coherent な join 余錐へ束ねる。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：指定ホモトピーの native な余錐と、その両端固定の比較データ。
方針：元の fat join 余錐との可逆な円柱を一つの構造に保持する。
規約：元の図式と指定頂点は厳密に一致する。使われ方：余錐の普遍性の追跡。 -/
structure HomotopyCoconeRealization (H : SSet.Homotopy f (SSet.const z)) where
  /-- 同じ図式上の native な余錐。 -/
  cocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f
  /-- 指定した頂点との厳密な一致。 -/
  vertex_eq : cocone.vertex = z
  /-- 元の fat join 表示との全ホモトピー。 -/
  comparison : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K Δ[0] ≫ cocone.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone H)
  /-- 元の図式と頂点を全時刻で固定する。 -/
  boundary : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K Δ[0]) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc f (SSet.yonedaEquiv.symm z)
  /-- 比較は各頂点で可逆。 -/
  vertical_isInvertible : ∀ v,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge comparison v).toTruncated

/-- 概要：定値頂点への指定ホモトピーを両端固定で native な余錐として実現する。
方針：既存の fat join の固定端点比較に元の全円柱を入力する。
規約：任意の形状と quasicategory 標的。使われ方：一般 coherent 図式の余錐。 -/
def homotopyCoconeRealization [Quasicategory X]
    (H : SSet.Homotopy f (SSet.const z)) : HomotopyCoconeRealization H := Classical.choice <| by
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc f (SSet.yonedaEquiv.symm z) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone H).app n a = f.app n a
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone_inl H) n) a
    | inr a =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone H).app n a =
        (SSet.yonedaEquiv.symm z).app n a
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone_inr H) n) a
  obtain ⟨G, hG, e, he, hI⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_joinDiagram_of_fatJoinDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc f (SSet.yonedaEquiv.symm z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyFatCocone H) hF
  have hGl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ G = f := by
    have h := congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K Δ[0] ≫ q) hG
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_inclusion] at h
    exact h
  have hGr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ G = SSet.yonedaEquiv.symm z := by
    have h := congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K Δ[0] ≫ q) hG
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_inclusion] at h
    exact h
  refine ⟨⟨⟨G, hGl⟩, ?_, e, he, hI⟩⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, hGr, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
