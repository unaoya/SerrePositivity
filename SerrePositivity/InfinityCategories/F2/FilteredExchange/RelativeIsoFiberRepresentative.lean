module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeIsoRepresentative
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FixedBaseHomotopyFiber

/-!
概要：元の底固定円柱の fiber 制限の実辺を、同じ相対代表辺の fiber Hom 像と照合する。
方針：Yoneda と curry/uncurry を往復し、全円柱の包含後の厳密な式で比較する。
規約：代表辺を再選択しない。使われ方：元の模型比較の fiber 内の指定類の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B)
  {f g : A ⟶ E} (hf : f ≫ p = a) (hg : g ≫ p = a)
  (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) (b : B _⦋0⦌)

/-- 同じ相対代表辺から作った元の底固定円柱の fiber 制限。 -/
def relativeIsoFiberHomotopy :=
  fixedBaseHomotopyFiber a p hf hg (relativeVertexIsoHomotopy p a hf hg e).val
    (relativeVertexIsoHomotopy p a hf hg e).property.1 b

/-- 元の全円柱は fiber の包含後に全時刻で同じ制限となる。 -/
lemma relativeIsoFiberHomotopy_h_ι :
    (relativeIsoFiberHomotopy p a hf hg e b).h ≫ vertexFiberι p b =
      (vertexFiberι a b ▷ (Δ[1] : SSet.{u})) ≫ (relativeVertexIsoHomotopy p a hf hg e).val.h := rfl

/-- fiber 円柱の実際の辺は同じ相対代表辺を fiber Hom へ写した同じ一次単体。 -/
lemma relativeIsoFiberHomotopy_edge :
    ((relativeIsoRepresentativeEdge p a hf hg e).map
      ((truncation 2).map (relativeFunctorFiberHom a p b))).edge =
      (functorEdgeOfSimplicialHomotopy (relativeIsoFiberHomotopy p a hf hg e b)).edge := by
  change (relativeFunctorFiberHom a p b).app (Opposite.op ⦋1⦌)
    (relativeIsoRepresentativeEdge p a hf hg e).edge =
      SSet.yonedaEquiv (curry (relativeIsoFiberHomotopy p a hf hg e b).h)
  apply (SSet.yonedaEquiv (X := (ihom (vertexFiber a b)).obj (vertexFiber p b))
    (n := ⦋1⦌)).symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  change SSet.yonedaEquiv.symm (relativeIsoRepresentativeEdge p a hf hg e).edge ≫
    relativeFunctorFiberHom a p b =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (curry (relativeIsoFiberHomotopy p a hf hg e b).h))
  rw [Equiv.symm_apply_apply]
  apply uncurry_injective
  rw [uncurry_curry]
  apply vertexFiber_hom_ext p b
  rw [relativeFunctorFiberHom_uncurry, relativeIsoFiberHomotopy_h_ι,
    relativeVertexIsoHomotopy_h_uncurry]
  rfl

end SerrePositivity.InfinityCategories.F2
