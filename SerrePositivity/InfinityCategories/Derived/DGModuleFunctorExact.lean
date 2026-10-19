module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorConePreservation
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberExists
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso

/-! # dg 加群間の dg 関手の完全性

概要：任意の dg 加群間の dg 関手の native nerve は完全である。
方針：標準 cone の保存を、同じ辺の cofiber 四角形の関手同型で全ての列へ移す。
規約：関手に追加の平坦性を要求しない。使われ方：β3 の Yoneda 模型による完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))

/-- 各実際の辺に、関手像も押し出しとなる cofiber 四角形を選べる。 -/
lemma dgModuleFunctor_cofiber_exists
    {x y : (dgModuleNerve A D) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y) :
    ∃ s : CofiberSquare e, IsPushoutSquare (s.square ≫ dgNerve.map F) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change ∃ s : CofiberSquare (X := dgModuleNerve A D)
    (e : Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)), _
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleCofiberSquare A D (edgeClosed e),
    dgModuleFunctorConeSquare_isPushout A D E F (edgeClosed e)⟩

/-- dg 加群間の dg 関手は、選択によらず任意の実 cofiber 列を保つ。 -/
theorem dgModuleFunctorNerve_preservesCofiber (t : ZeroTriangle (dgModuleNerve A D))
    (ht : IsCofiberSequence t) :
    IsCofiberSequence (t.map (dgNerve.map F) (dgFunctorNerve_preservesZeroVertices F)) := by
  let f := edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ t.square))
  let s : CofiberSquare f := {
    toZeroTriangle := t
    bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  obtain ⟨r, hr⟩ := dgModuleFunctor_cofiber_exists A D E F f
  obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso r s
  exact hr.of_functorIso (e.postcomp (dgNerve.map F))

/-- 任意の dg 加群間の dg 関手の native nerve は完全である。 -/
theorem dgModuleFunctorNerve_isExactFunctor : IsExactFunctor (dgNerve.map F) where
  preservesZero := dgFunctorNerve_preservesZeroVertices F
  preservesCofiber := dgModuleFunctorNerve_preservesCofiber A D E F

end SerrePositivity.InfinityCategories
