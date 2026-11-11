module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pasting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-!
概要：同じ 3×3 図式の四面から外側の押し出し性を得る。
方針：実際の長方形の貼り合わせと同じ図式の評価を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def grid22Face {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶ X) (i j : Fin 3) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare ((Δ[2] ◁ stdSimplex.δ j) ≫ F) i

def grid22VerticalStrip {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶ X) (i : Fin 3) :
    (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  (β_ Δ[2] Δ[1]).hom ≫ (stdSimplex.δ i ▷ Δ[2]) ≫ F

lemma grid22VerticalStrip_face {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶ X) (i j : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (grid22VerticalStrip F i) j =
      (β_ Δ[1] Δ[1]).hom ≫ grid22Face F i j := by
  have h : (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[2] Δ[1]).hom ≫
      (stdSimplex.δ i ▷ Δ[2]) =
      (β_ Δ[1] Δ[1]).hom ≫ (stdSimplex.δ i ▷ Δ[1]) ≫ (Δ[2] ◁ stdSimplex.δ j) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, grid22VerticalStrip, grid22Face, Category.assoc] using
    congrArg (fun f ↦ f ≫ F) h

lemma isPushoutSquare_grid22_outer {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶ X)
    (h22 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 2 2))
    (h02 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 0 2))
    (h20 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 2 0))
    (h00 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 1 1) := by
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 1 2) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting ((Δ[2] ◁ stdSimplex.δ 2) ≫ F) h22 h02
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (grid22Face F 1 0) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting ((Δ[2] ◁ stdSimplex.δ 0) ≫ F) h20 h00
  have hvb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (grid22VerticalStrip F 1) 2) := by
    rw [grid22VerticalStrip_face]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp hb
  have hvt : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (grid22VerticalStrip F 1) 0) := by
    rw [grid22VerticalStrip_face]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp ht
  have ho := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting (grid22VerticalStrip F 1) hvb hvt
  rw [grid22VerticalStrip_face] at ho
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mpr ho

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
