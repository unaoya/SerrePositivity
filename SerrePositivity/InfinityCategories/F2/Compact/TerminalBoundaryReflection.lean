module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTerminalHom

/-!
概要：相対終点境界充填を持つ元の二頂点の間では、元の射が辺の可逆性を反映する。
方針：元の h の Hom 比較の全単射で逆射を持ち上げ、両三角式を単射性で反映する。
規約：指定辺とその同じ像を保持。使われ方：極限錐の全比較の底図式からの反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の両端が相対終点なら、底で可逆な同じ比較辺は元の圏でも可逆。 -/
lemma terminalBoundary_reflects_invertibleEdge {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B)
    {a b : E _⦋0⦌} (ha : TerminalBoundaryLifting p a)
    (hb : TerminalBoundaryLifting p b) (e : E.Edge a b)
    (he : IsInvertibleEdge (e.map p)) : IsInvertibleEdge e := by
  let F := (hoFunctor.map p).toFunctor
  let m := SSet.HomotopyCategory.homMk e
  have hm : IsIso (F.map m) := he
  have := hm
  have hMap := HomotopyLimits.homMap_bijective_of_terminalBoundaryLifting p a ha b
  obtain ⟨n, hn⟩ := hMap.surjective (inv (F.map m))
  change IsIso m
  refine ⟨⟨n, ?_, ?_⟩⟩
  · apply (HomotopyLimits.homMap_bijective_of_terminalBoundaryLifting p a ha a).injective
    change F.map (m ≫ n) = F.map (𝟙 _)
    rw [F.map_comp, hn, IsIso.hom_inv_id, F.map_id]
  · apply (HomotopyLimits.homMap_bijective_of_terminalBoundaryLifting p b hb b).injective
    change F.map (n ≫ m) = F.map (𝟙 _)
    rw [F.map_comp, hn, IsIso.inv_hom_id, F.map_id]

end SerrePositivity.InfinityCategories.F2.Compact
