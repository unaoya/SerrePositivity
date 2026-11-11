module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の指定円柱が時間方向に定値なら、その辺の類の指定同型は等式から来る。
方針：curry した辺を定値辺へ厳密に同定する。
規約：指定された同型を保持。使われ方：path 置換の切断上の比較の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：時間に定値な元の円柱の辺の類は等式から来る同型。
方針：curry と定値辺の識別。規約：元の値。使われ方：切断上の標準同型の判定。 -/
lemma isFunctorEqIso_of_homotopy_constant {A Y : SSet.{u}} {f g : A ⟶ Y}
    (H : SSet.Homotopy f g) (e : FunctorIso f g)
    (he : e.hom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
    (h : H.h = fst A (Δ[1] : SSet.{u}) ≫ f) : IsFunctorEqIso e := by
  apply isFunctorEqIso_of_constant_edge e
    (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H)) he
  change SSet.yonedaEquiv (curry H.h) = PinchedHom.constant (functorVertex f) 1
  rw [h]
  have hc : curry (fst A (Δ[1] : SSet.{u}) ≫ f) =
      (SSet.const (functorVertex f) : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj Y) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_const_functorVertex]
  rw [hc]
  exact pinchedConstant_one (functorVertex f)

end SerrePositivity.InfinityCategories.F2
