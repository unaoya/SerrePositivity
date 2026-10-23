module

public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：quasicategory 間の可逆な二胞体と同値の宇宙持ち上げ。
方針：可逆な二胞体を点ごとに可逆なホモトピーとして持ち上げ、同じ逆射のデータを得る。
規約：Kan 複体に制限せず、全ての quasicategory の比較に適用する。
使われ方：Kerodon Corollary 5.6.0.6、strict transport と coherent な復元の宇宙を揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：平行な関手の可逆な二胞体を宇宙持ち上げする。
方針：二胞体を表す辺のホモトピーを持ち上げ、各頂点での辺の可逆性を写す。
規約：標的は quasicategory、定義域は任意。
使われ方：Kerodon Corollary 5.6.0.6、全空間の同値の単位・余単位の持ち上げ。 -/
noncomputable def FunctorIso.ulift {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) :
    FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) :=
  functorIsoOfPointwiseInvertibleHomotopy (uliftSimplicialHomotopy e.simplicialHomotopy) (by
    rintro ⟨x⟩
    rw [uliftSimplicialHomotopy_vertexEdge]
    exact (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) x).ulift)

/-- 概要：quasicategory 間の同値は宇宙持ち上げで保存される。
方針：逆射と二つの可逆二胞体を同じ関手で持ち上げる。
規約：追加の宇宙 v は任意。Kan 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、元の全空間と 𝒮 値 unstraightening の比較。 -/
lemma IsQCatEquivalence.ulift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsQCatEquivalence f) :
    IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f) := by
  obtain ⟨g, ⟨h₀⟩, ⟨h₁⟩⟩ := hf
  refine ⟨(SSet.uliftFunctor.{v, u}).map g, ⟨?_⟩, ⟨?_⟩⟩
  · have h := FunctorIso.ulift.{u, v} h₀
    rw [(SSet.uliftFunctor.{v, u}).map_comp, (SSet.uliftFunctor.{v, u}).map_id] at h
    exact h
  · have h := FunctorIso.ulift.{u, v} h₁
    rw [(SSet.uliftFunctor.{v, u}).map_comp, (SSet.uliftFunctor.{v, u}).map_id] at h
    exact h

end SerrePositivity.InfinityCategories
