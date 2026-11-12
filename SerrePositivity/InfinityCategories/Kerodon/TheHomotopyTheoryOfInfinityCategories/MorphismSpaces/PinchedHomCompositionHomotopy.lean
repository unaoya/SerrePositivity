module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 実 pinched 合成による二つの全ホモトピーの同時合成

概要：二つの係数族の実ホモトピーを、同じ全時刻で AW 合成する。
方針：円柱上の二写像を同じ合成族へ送り、両端を族の前合成自然性で照合する。
規約：ホモトピー類から選び直さない。使われ方：実屋根の入力比較の同時合成。

対応節は Kerodon 4.6（Tag 01J3）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 指定された二つの実ホモトピーを、全時刻の写像ごと同時に合成する。 -/
def pinchedHomCompositionHomotopy {K : SSet.{max u v}} {x y z : D}
    {f f' : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y} {g g' : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z}
    (H : SSet.Homotopy f f') (J : SSet.Homotopy g g') :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f' g') where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily H.h J.h
  h₀ := by
    change SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily H.h J.h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f g
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_precomp, H.h₀, J.h₀]
  h₁ := by
    change SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily H.h J.h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f' g'
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_precomp, H.h₁, J.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 両入力が指定部分を全時刻固定すれば、同じ実合成ホモトピーもその合成を全時刻固定する。 -/
lemma pinchedHomCompositionHomotopy_fixed {K L : SSet.{max u v}} {x y z : D}
    {f f' : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y} {g g' : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z}
    (H : SSet.Homotopy f f') (J : SSet.Homotopy g g') (i : L ⟶ K)
    (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z)
    (hH : (i ▷ (Δ[1] : SSet.{max u v})) ≫ H.h = fst L Δ[1] ≫ a)
    (hJ : (i ▷ (Δ[1] : SSet.{max u v})) ≫ J.h = fst L Δ[1] ≫ b) :
    (i ▷ (Δ[1] : SSet.{max u v})) ≫ (pinchedHomCompositionHomotopy H J).h =
      fst L Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily a b := by
  change (i ▷ (Δ[1] : SSet.{max u v})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily H.h J.h = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_precomp, hH, hJ, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_precomp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
