module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.F2.VertexIsoTerminalEquality

/-!
概要：相対 curry の豊穣作用と、元の始域の制限を厳密に交換する。
方針：二段階の評価の全座標を計算し、同じ射の等式で指定頂点同型を写す。
規約：係数の全単体を保持。使われ方：元の prism の指定比較を各点の作用へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) (s : C ⟶ A)

/-- 相対 curry の前に始域を制限しても、後で相対関手を制限しても同じ射。 -/
lemma relativeFunctorCurryHom_pre :
    relativeFunctorPre p (fst A L ≫ a) (s ▷ L) ≫ relativeFunctorCurryHom p (s ≫ a) L =
      relativeFunctorCurryHom p a L ≫ (ihom L).map (relativeFunctorPre p a s) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  dsimp only [relativeFunctorCurryHom]
  rw [uncurry_curry, uncurry_curry]
  apply relativeFunctorUncurry_injective p (s ≫ a)
  rw [relativeFunctorUncurry_naturality, relativeFunctorUncurry_curry]
  change _ = relativeFunctorUncurry
    (relativeFunctorCurry _ _ ≫ relativeFunctorOverPre p
      (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl))
  rw [relativeFunctorOverPre_uncurry, relativeFunctorUncurry_curry]
  let S := relativeFunctorSpace p (fst A L ≫ a)
  let Q := relativeFunctorSpace p (fst C L ≫ s ≫ a)
  let t := relativeFunctorPre p (fst A L ≫ a) (s ▷ L)
  have h : (C ◁ (L ◁ t)) ≫ (α_ C L Q).inv =
      (α_ C L S).inv ≫ ((C ⊗ L) ◁ t) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, h, Category.assoc, ← relativeFunctorUncurry_naturality]
  have ht : relativeFunctorUncurry (t ≫ 𝟙 Q) =
      ((s ▷ L) ▷ S) ≫ relativeFunctorUncurry (𝟙 S) := by
    change relativeFunctorUncurry ((𝟙 S) ≫ relativeFunctorOverPre p
      (Over.homMk (U := Over.mk (fst C L ≫ s ≫ a))
        (V := Over.mk (fst A L ≫ a)) (s ▷ L) rfl)) = _
    exact relativeFunctorOverPre_uncurry p _ _
  rw [ht, ← Category.assoc, ← Category.assoc]
  congr 1

/-- 指定頂点同型の相対 curry と始域制限は、同じ指定値を保って交換する。 -/
lemma relativeFunctorCurryHom_vertexIso_pre
    {x y : (relativeFunctorSpace p (fst A L ≫ a)) _⦋0⦌} (e : VertexIso x y) :
    HEq
      (VertexIso.map (VertexIso.map e (relativeFunctorPre p (fst A L ≫ a) (s ▷ L)))
        (relativeFunctorCurryHom p (s ≫ a) L))
      (VertexIso.map (VertexIso.map e (relativeFunctorCurryHom p a L))
        ((ihom L).map (relativeFunctorPre p a s))) := by
  exact (heq_of_eq (vertexIso_map_comp e
    (relativeFunctorPre p (fst A L ≫ a) (s ▷ L)) (relativeFunctorCurryHom p (s ≫ a) L))).trans
      ((vertexIso_map_heq e (relativeFunctorCurryHom_pre p a L s)).trans
        (heq_of_eq (vertexIso_map_comp e (relativeFunctorCurryHom p a L)
          ((ihom L).map (relativeFunctorPre p a s)))).symm)

end SerrePositivity.InfinityCategories.F2
