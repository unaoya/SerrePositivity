module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomComposition
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-! # 実 pinched 合成による二つの全ホモトピーの同時合成

概要：二つの係数族の実ホモトピーを、同じ全時刻で AW 合成する。
方針：円柱上の二写像を同じ合成族へ送り、両端を族の前合成自然性で照合する。
規約：ホモトピー類から選び直さない。使われ方：実屋根の入力比較の同時合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 指定された二つの実ホモトピーを、全時刻の写像ごと同時に合成する。 -/
def pinchedHomCompositionHomotopy {K : SSet.{max u v}} {x y z : D}
    {f f' : K ⟶ DGNerve.pinchedHom A D x y} {g g' : K ⟶ DGNerve.pinchedHom A D y z}
    (H : SSet.Homotopy f f') (J : SSet.Homotopy g g') :
    SSet.Homotopy (pinchedHomCompositionFamily f g) (pinchedHomCompositionFamily f' g') where
  h := pinchedHomCompositionFamily H.h J.h
  h₀ := by
    change SSet.ι₀ ≫ pinchedHomCompositionFamily H.h J.h = pinchedHomCompositionFamily f g
    rw [pinchedHomCompositionFamily_precomp, H.h₀, J.h₀]
  h₁ := by
    change SSet.ι₁ ≫ pinchedHomCompositionFamily H.h J.h = pinchedHomCompositionFamily f' g'
    rw [pinchedHomCompositionFamily_precomp, H.h₁, J.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 両入力が指定部分を全時刻固定すれば、同じ実合成ホモトピーもその合成を全時刻固定する。 -/
lemma pinchedHomCompositionHomotopy_fixed {K L : SSet.{max u v}} {x y z : D}
    {f f' : K ⟶ DGNerve.pinchedHom A D x y} {g g' : K ⟶ DGNerve.pinchedHom A D y z}
    (H : SSet.Homotopy f f') (J : SSet.Homotopy g g') (i : L ⟶ K)
    (a : L ⟶ DGNerve.pinchedHom A D x y) (b : L ⟶ DGNerve.pinchedHom A D y z)
    (hH : (i ▷ (Δ[1] : SSet.{max u v})) ≫ H.h = fst L Δ[1] ≫ a)
    (hJ : (i ▷ (Δ[1] : SSet.{max u v})) ≫ J.h = fst L Δ[1] ≫ b) :
    (i ▷ (Δ[1] : SSet.{max u v})) ≫ (pinchedHomCompositionHomotopy H J).h =
      fst L Δ[1] ≫ pinchedHomCompositionFamily a b := by
  change (i ▷ (Δ[1] : SSet.{max u v})) ≫ pinchedHomCompositionFamily H.h J.h = _
  rw [pinchedHomCompositionFamily_precomp, hH, hJ, ← pinchedHomCompositionFamily_precomp]

end SerrePositivity.InfinityCategories
