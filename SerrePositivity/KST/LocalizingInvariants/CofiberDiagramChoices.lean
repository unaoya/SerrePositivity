module

public import SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

/-!
概要：元の任意の矢印族の普遍 cofiber 図式への lift と、底辺・右辺評価の頂点全射性。
方針：既存の coherent な cofiber 選択と、安定性の指定 fiber 四角形を使う。
規約：元の指定辺を厳密に保つ。使われ方：二つの評価の境界持ち上げの零次元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

def lift {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) : A ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X :=
  fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a) (by
    intro x
    exact ⟨_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_zero X a x, _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_isPushout X a x⟩)

lemma lift_inclusion {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    lift X a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X = _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a := fullSubcomplexLift_ι _ _ _

lemma lift_bottom {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    lift X a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X = a := by
  change lift X a ≫ (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.inclusion X ≫ (pre squareBottomEdge).app X) = _
  rw [← Category.assoc, lift_inclusion, _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares_bottom]

lemma bottom_surjective : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X).app (Opposite.op ⦋0⦌)) := by
  intro x
  let s := chosenCofiberSquare (edgeOfSimplex (intervalFunctorVertexEdge x))
  let v : (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X) _⦋0⦌ := ⟨functorVertex s.square, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    unfold _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate
    rw [squareDiagram_functorVertex]
    exact ⟨s.zero_corner, s.isPushout⟩⟩
  refine ⟨v, ?_⟩
  change functorVertex (squareBottomEdge ≫ s.square) = x
  rw [s.bottom_edge]
  change functorVertex (SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((functorVertexEquiv Δ[1] X).symm x))) = x
  rw [Equiv.symm_apply_apply]
  exact (functorVertexEquiv Δ[1] X).apply_symm_apply x

lemma right_surjective : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X).app (Opposite.op ⦋0⦌)) := by
  intro x
  let s := chosenFiberSquare (edgeOfSimplex (intervalFunctorVertexEdge x))
  let v : (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X) _⦋0⦌ := ⟨functorVertex s.square, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    unfold _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.Predicate
    rw [squareDiagram_functorVertex]
    exact ⟨s.zero_corner, IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback⟩⟩
  refine ⟨v, ?_⟩
  change functorVertex (squareRightEdge ≫ s.square) = x
  rw [s.right_edge]
  change functorVertex (SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((functorVertexEquiv Δ[1] X).symm x))) = x
  rw [Equiv.symm_apply_apply]
  exact (functorVertexEquiv Δ[1] X).apply_symm_apply x

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
