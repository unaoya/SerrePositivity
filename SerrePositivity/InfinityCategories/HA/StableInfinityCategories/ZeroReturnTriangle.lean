module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 零頂点へ戻る合成二単体

概要：零対象から出る辺は、零対象へ戻る辺と恒等辺を長辺とする合成二単体を持つ。
方針：零対象からの Hom の一意性を合成二単体に持ち上げる。
規約：長辺を実際の恒等辺に固定する。使われ方：和の包含の cofiber 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零頂点からの辺を恒等辺へ戻る合成二単体に延長できる。
方針：終対象性で戻り辺を選び、零対象からの射の一意性を二単体へ持ち上げる。
規約：値域は quasicategory、安定性は不要。使われ方：零始点の押し出しの延長。 -/
lemma exists_zeroReturnTriangle {X : SSet.{u}} [Quasicategory X]
    {z x : X _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) z x) :
    ∃ τ : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ τ = SSet.yonedaEquiv.symm f.edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ τ = SSet.const z := by
  let g := Classical.choice (hz.2.nonempty_edge x)
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) z
  have h : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g = SSet.Truncated.HomotopyCategory.homMk e :=
    hz.isZeroHo.eq_of_src _ _
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h
  refine ⟨SSet.yonedaEquiv.symm t.simplex, ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 1 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₁.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one z).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
