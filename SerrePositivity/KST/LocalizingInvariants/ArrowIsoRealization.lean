module

public import SerrePositivity.InfinityCategories.Stable.HomotopyInvertibility

/-!
概要：h 圏の可換四角形で指定した縦辺が同値なら、元の二辺の関手同型を構成する。
方針：四辺固定の実ホモトピーを実現し、両端点での可逆性で区間関手の辺を判定する。
規約：通常矢印圏の同型だけに留めない。使われ方：商の分数表示から矢印図式への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma arrowFunctorIso_of_homMk_comm {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : Truncated.Edge (X := (truncation 2).obj X) x x')
    (b : Truncated.Edge (X := (truncation 2).obj X) y y')
    (ha : IsInvertibleEdge a) (hb : IsInvertibleEdge b)
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫
        SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ SSet.Truncated.HomotopyCategory.homMk g) :
    Nonempty (FunctorIso (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)) := by
  obtain ⟨H, h₀, h₁⟩ := exists_arrowHomotopy_of_homMk_comm f g a b h
  have := arrowHomotopy_isInvertible_of_endpointPaths H a b ha hb h₀ h₁
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))⟩

/-- 縦辺を h 圏内の同型で与えた場合も、元の二つの実辺の関手同型へ移せる。 -/
lemma arrowFunctorIso_of_vertexIso_comm {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : VertexIso x x') (b : VertexIso y y')
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫ b.hom =
      a.hom ≫ SSet.Truncated.HomotopyCategory.homMk g) :
    Nonempty (FunctorIso (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)) := by
  obtain ⟨s, hs⟩ := homotopyCategory_homMk_surjective x x' a.hom
  obtain ⟨t, ht⟩ := homotopyCategory_homMk_surjective y y' b.hom
  have hs' : IsInvertibleEdge s := by rw [IsInvertibleEdge, hs]; infer_instance
  have ht' : IsInvertibleEdge t := by rw [IsInvertibleEdge, ht]; infer_instance
  exact arrowFunctorIso_of_homMk_comm f g s t hs' ht' (by simpa only [hs, ht] using h)

end SerrePositivity.KST.LocalizingInvariants
