module

public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyRoundTrip

/-!
概要：元の矢印族を、その prism を変えず自然変換として読む。
方針：uncurry と対称性を使い、端点評価と各頂点の辺を照合する。
規約：代表辺を選び直さない。使われ方：cofiber の指定された右辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def arrowFamilyHomotopy {A X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    SSet.Homotopy (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ uncurry a
  h₀ := by
    change SSet.ι₀ ≫ _ = a ≫ _
    rw [← curry_uncurry a, curry_evaluateFunctorAt_interval, uncurry_curry]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ _ = a ≫ _
    rw [← curry_uncurry a, curry_evaluateFunctorAt_interval, uncurry_curry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

lemma arrowFamilyHomotopy_roundTrip {A X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    ZeroArrowFamily.ofHomotopy (arrowFamilyHomotopy a) = a :=
  ZeroArrowFamily.ofHomotopy_eq_of_h _ a rfl

lemma arrowFamilyHomotopy_vertex_edge {A X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (x : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (arrowFamilyHomotopy a) x).edge =
      intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x) := by
  conv_rhs => rw [← arrowFamilyHomotopy_roundTrip a]
  rw [ZeroArrowFamily.ofHomotopy, intervalFunctorVertexEdge_curry]
  change (arrowFamilyHomotopy a).h.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge, homotopyIntervalEdge.edge) =
      (arrowFamilyHomotopy a).h.app (Opposite.op ⦋1⦌)
        (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [pinchedConstant_one, hi]

end SerrePositivity.KST.LocalizingInvariants
