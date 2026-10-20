module
public import SerrePositivity.InfinityCategories.Stable.CofiberHoDenominators
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-! # 実屋根の合成のための Ore 細分

概要：任意の実辺と同じ終点に入る実 Verdier 分母を、指定二辺を保った実三角形で細分する。
方針：三角的分母の右分数計算を実辺へ戻し、共通対角辺と二つの実合成三角形を作る。
規約：通常の閉分母圏の filteredness や実四角形の引き戻し性は仮定しない。
使われ方：実屋根を合成する共通細分の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ終点への任意辺と分母の、実分母を左脚とする共通細分。 -/
structure ActualRoofOreRefinement {X : SSet.{u}} (W : Set (X _⦋1⦌))
    {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (s : Truncated.Edge (X := (truncation 2).obj X) y z) where
  apex : X _⦋0⦌
  denominator : Truncated.Edge (X := (truncation 2).obj X) apex x
  denominator_mem : denominator.edge ∈ W
  lift : Truncated.Edge (X := (truncation 2).obj X) apex y
  diagonal : Truncated.Edge (X := (truncation 2).obj X) apex z
  firstTriangle : Truncated.Edge.CompStruct denominator f diagonal
  secondTriangle : Truncated.Edge.CompStruct lift s diagonal

/-- 安定 ∞ 圏の cofiber 分母は、指定実辺と指定対角辺を持つ Ore 細分を与える。 -/
theorem cofiberStableEdges_actualOreRefinement_nonempty {X : SSet.{u}}
    [Quasicategory X] [IsStable X] (P : Set (X _⦋0⦌)) {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (s : Truncated.Edge (X := (truncation 2).obj X) y z)
    (hs : s.edge ∈ cofiberLocalizingEdges {a | StableVertexClosure P a}) :
    Nonempty (ActualRoofOreRefinement (cofiberLocalizingEdges
      {a | StableVertexClosure P a}) f s) := by
  have : (stableHoClosure P).trW.IsMultiplicative := inferInstance
  let φ : (stableHoClosure P).trW.LeftFraction (SSet.HomotopyCategory.mk x)
      (SSet.HomotopyCategory.mk y) :=
    ⟨Truncated.HomotopyCategory.homMk f, Truncated.HomotopyCategory.homMk s,
      (cofiberStableEdges_iff_trW P s).mp hs⟩
  obtain ⟨ψ, hψ⟩ := φ.exists_rightFraction
  obtain ⟨q, hq⟩ := SSet.Truncated.HomotopyCategory.mk_surjective ψ.X'
  let e := eqToIso hq
  obtain ⟨t, ht⟩ := homotopyCategory_homMk_surjective q x (e.hom ≫ ψ.s)
  obtain ⟨g, hg⟩ := homotopyCategory_homMk_surjective q y (e.hom ≫ ψ.f)
  obtain ⟨h, hh⟩ := homotopyCategory_homMk_surjective q z
    (Truncated.HomotopyCategory.homMk t ≫ Truncated.HomotopyCategory.homMk f)
  have htW : t.edge ∈ cofiberLocalizingEdges {a | StableVertexClosure P a} := by
    apply (cofiberStableEdges_iff_trW P t).mpr
    rw [ht]
    exact MorphismProperty.comp_mem _ _ _ ((stableHoClosure P).trW_of_isIso e.hom) ψ.hs
  have hfirst : Nonempty (Truncated.Edge.CompStruct t f h) :=
    compStruct_nonempty_of_homMk_fac hh.symm
  have hsecond : Nonempty (Truncated.Edge.CompStruct g s h) := by
    apply compStruct_nonempty_of_homMk_fac
    rw [hg, hh, ht]
    simpa only [φ, Category.assoc] using (congrArg (fun v => e.hom ≫ v) hψ).symm
  exact ⟨⟨q, t, htW, g, h, hfirst.some, hsecond.some⟩⟩

end SerrePositivity.InfinityCategories
