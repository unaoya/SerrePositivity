module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpecifiedEdgeTriangleBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension

/-!
概要：相対終対象へ向かう指定三辺を、元の底を固定する比較三角形に充填する。
方針：三辺の境界を貼り、相対終点境界充填の二次元の場合を適用する。
規約：三辺と底の全二単体を保持。使われ方：部分極限比較の二次の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対終対象への指定された三辺は、同じ底の上の全三角形として充填できる。 -/
lemma relativeTerminal_triangle {E D : SSet.{u}} (p : E ⟶ D) (b : D _⦋0⦌)
    {x y z : E _⦋0⦌} (hz : TerminalBoundaryLifting p z)
    (e : E.Edge x y) (f : E.Edge y z) (g : E.Edge x z)
    (he : SSet.yonedaEquiv.symm e.edge ≫ p = SSet.const b)
    (hf : SSet.yonedaEquiv.symm f.edge ≫ p = SSet.const b)
    (hg : SSet.yonedaEquiv.symm g.edge ≫ p = SSet.const b) :
    ∃ T : (Δ[2] : SSet.{u}) ⟶ E,
      stdSimplex.δ (0 : Fin 3) ≫ T = SSet.yonedaEquiv.symm f.edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ T = SSet.yonedaEquiv.symm g.edge ∧
      stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm e.edge ∧ T ≫ p = SSet.const b := by
  let a := specifiedEdgeTriangleBoundary e f g
  have ha : a ≫ p = SSet.const b := by
    dsimp only [a]
    apply boundary.hom_ext
    intro i
    fin_cases i
    · change (boundary.ι (0 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g) ≫ p =
        boundary.ι (0 : Fin 3) ≫ SSet.const b
      rw [specifiedEdgeTriangleBoundary_zero, SSet.comp_const]
      exact hf
    · change (boundary.ι (1 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g) ≫ p =
        boundary.ι (1 : Fin 3) ≫ SSet.const b
      rw [specifiedEdgeTriangleBoundary_one, SSet.comp_const]
      exact hg
    · change (boundary.ι (2 : Fin 3) ≫ specifiedEdgeTriangleBoundary e f g) ≫ p =
        boundary.ι (2 : Fin 3) ≫ SSet.const b
      rw [specifiedEdgeTriangleBoundary_two, SSet.comp_const]
      exact he
  have sq : CommSq a (boundary 2).ι p (SSet.const b) := by
    constructor
    rw [ha, SSet.comp_const]
  obtain ⟨T, hT, hp⟩ := hz 1 a (SSet.const b) (specifiedEdgeTriangleBoundary_last e f g) sq
  refine ⟨T, ?_, ?_, ?_, hp⟩
  · have h := congrArg (fun q => boundary.ι (0 : Fin 3) ≫ q) hT
    dsimp only [a] at h
    rwa [← Category.assoc, boundary.ι_ι, specifiedEdgeTriangleBoundary_zero] at h
  · have h := congrArg (fun q => boundary.ι (1 : Fin 3) ≫ q) hT
    dsimp only [a] at h
    rwa [← Category.assoc, boundary.ι_ι, specifiedEdgeTriangleBoundary_one] at h
  · have h := congrArg (fun q => boundary.ι (2 : Fin 3) ≫ q) hT
    dsimp only [a] at h
    rwa [← Category.assoc, boundary.ι_ι, specifiedEdgeTriangleBoundary_two] at h

end SerrePositivity.InfinityCategories.F2
