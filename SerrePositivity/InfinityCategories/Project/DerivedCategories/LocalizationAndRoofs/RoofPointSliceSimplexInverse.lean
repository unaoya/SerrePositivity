module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofPointSliceSimplex

/-! # 終点固定単体と指定零面からの任意次元の実 over 回収

概要：最後の頂点を固定する元の実単体を、実 over 単体へ戻し全面を照合する。
方針：点との join 同型を逆に使い、指定零面から最後の頂点の固定を得る。
規約：入力は実単体と実面の等式。使われ方：一般細分最後ホーン充填の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 最後の頂点が指定点に固定された実単体を、実 over 単体へ戻す。 -/
def roofPointSliceSimplexOfFixed {n : ℕ} (F : Δ[n + 1] ⟶ X)
    (hF : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) ≫ F = a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
    exact hF⟩

/-- 回収した over 単体を再び元へ移すと、入力単体そのものになる。 -/
lemma roofPointSliceSimplexOfFixed_simplex {n : ℕ} (F : Δ[n + 1] ⟶ X)
    (hF : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) ≫ F = a) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a (roofPointSliceSimplexOfFixed a F hF) = F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ F) = F
  rw [Iso.inv_hom_id_assoc]

/-- 指定 over 零面を持つ一つ上の実単体から、実 over 単体を回収する。 -/
def roofPointSliceSimplexOfFace {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) (F : Δ[n + 2] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n + 1⦌ :=
  roofPointSliceSimplexOfFixed a F (by
    have he : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex (n + 1)) =
        SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) ≫
          SSet.stdSimplex.δ (0 : Fin (n + 3)) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
    rw [he, Category.assoc, h₀]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_fixed a σ)

/-- 指定零面から回収した実 over 単体は、元の実充填そのものを与える。 -/
lemma roofPointSliceSimplexOfFace_simplex {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌)
    (F : Δ[n + 2] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a (roofPointSliceSimplexOfFace a σ F h₀) = F :=
  roofPointSliceSimplexOfFixed_simplex a F _

/-- 回収した実 over 単体の全面は、元の単体の最終面以外の同じ面となる。 -/
lemma roofPointSliceSimplexOfFace_face {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌)
    (F : Δ[n + 2] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)
    (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ i (roofPointSliceSimplexOfFace a σ F h₀)) =
      SSet.stdSimplex.δ i.castSucc ≫ F := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_face, roofPointSliceSimplexOfFace_simplex]

/-- 回収した実 over 単体の零面は、入力の同じ指定 over 単体。 -/
lemma roofPointSliceSimplexOfFace_face_zero {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌)
    (F : Δ[n + 2] ⟶ X)
    (h₀ : SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ (0 : Fin (n + 2)) (roofPointSliceSimplexOfFace a σ F h₀) = σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  exact (roofPointSliceSimplexOfFace_face a σ F h₀ 0).trans h₀

end SerrePositivity.InfinityCategories.Project.DerivedCategories
