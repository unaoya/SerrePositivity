module

public import SerrePositivity.InfinityCategories.F1.Categories.CoreProduct
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：関手の同型を元の core 間の関手の同型へ移す。
方針：可逆な関手の辺を内部 Hom の core に入れ、core の積と元の評価で作用させる。
規約：元の core 写像そのものを両端に持つホモトピーを構成する。
使われ方：cocartesian strict transport の Hom 比較を core の Hom 比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 可逆な自然変換の辺は内部 Hom の core 内の標準区間を与える。 -/
def functorIsoCoreInterval {A E : SSet.{u}} [Quasicategory E]
    {f g : A ⟶ E} (h : FunctorIso f g) :
    (Δ[1] : SSet.{u}) ⟶ (quasicategoryCore ((ihom A).obj E) : SSet.{u}) :=
  SSet.yonedaEquiv.symm ⟨h.edge.edge, (quasicategoryCore_mem_edge_iff _).mpr
    ((isInvertibleEdge_congr (e := h.edge) (f := edgeOfSimplex h.edge.edge) rfl).mp
      h.edge_isInvertible)⟩

/-- 関手同型の core 上の作用は、元のホモトピーを core に厳密に持ち上げる。 -/
def functorIsoCoreHomotopy {A E : SSet.{u}} [Quasicategory E]
    {f g : A ⟶ E} (h : FunctorIso f g) :
    SSet.Homotopy (quasicategoryCoreMap f) (quasicategoryCoreMap g) := by
  let K := (quasicategoryCore A : SSet.{u})
  let H : K ⊗ (Δ[1] : SSet.{u}) ⟶ (quasicategoryCore E : SSet.{u}) :=
    (K ◁ functorIsoCoreInterval h) ≫ quasicategoryCoreProduct A ((ihom A).obj E) ≫
      quasicategoryCoreMap (uncurry (𝟙 ((ihom A).obj E)))
  have hH : H ≫ (quasicategoryCore E).ι =
      ((quasicategoryCore A).ι ▷ (Δ[1] : SSet.{u})) ≫ h.simplicialHomotopy.h := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  refine { h := H, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · apply (cancel_mono (quasicategoryCore E).ι).mp
    rw [Category.assoc, hH, ← Category.assoc, SSet.ι₀_comp, Category.assoc,
      h.simplicialHomotopy.h₀]
    exact (quasicategoryCoreMap_ι f).symm
  · apply (cancel_mono (quasicategoryCore E).ι).mp
    rw [Category.assoc, hH, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
      h.simplicialHomotopy.h₁]
    exact (quasicategoryCoreMap_ι g).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 関手の同型は、同じ元の core 写像間の関手同型を与える。 -/
def FunctorIso.core {A E : SSet.{u}} [Quasicategory E]
    {f g : A ⟶ E} (h : FunctorIso f g) :
    FunctorIso (quasicategoryCoreMap f) (quasicategoryCoreMap g) :=
  functorIsoOfSimplicialHomotopy (functorIsoCoreHomotopy h)

end SerrePositivity.InfinityCategories
