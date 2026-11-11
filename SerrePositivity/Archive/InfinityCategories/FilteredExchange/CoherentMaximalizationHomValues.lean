module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexStrictification
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomMono

/-!
概要：最大化した coherent 単体の全 Hom の作用を strict な射列の定値単体として読む。
方針：最大化と順序図式の等式から、同じ二対象間の Hom の作用を取り出す。
規約：元の path の全次数を保持し、通常の射は最大 path の像を使う。
使われ方：最大化側の最後辺の全係数を、元の二辺の合成と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：最大化の Hom の各単体は strict な射の定値単体。
方針：等しい豊穣関手から同じ対象間の Hom の等式を取り出す。
規約：任意の単体的圏と全次数の path を扱う。
使われ方：最後辺の head に現れる最大化の作用を計算する。 -/
lemma coherentSimplexMaximalization_map_constant
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n d : ℕ} (s : (SimplicialNerve C) _⦋n⦌)
    (i j : SimplicialThickening (ULift.{u} (Fin (n + 1))))
    (P : (SimplicialCategory.sHom i j) _⦋d⦌) :
    ((coherentSimplexMaximalization s).map i j).app (Opposite.op ⦋d⦌) P =
      PinchedHom.constant (SimplicialCategory.homEquiv' _ _
        ((coherentSimplexStrictDiagram s).map (homOfLE (Path.le (P.obj 0))))) d := by
  have h := eq_of_heq (enrichedFunctor_map_heq
    (coherentSimplexMaximalization_eq_strictDiagram s) i j)
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.F2
