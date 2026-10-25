module

public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialSimplexPrefix
public import SerrePositivity.InfinityCategories.Core.JoinComparisonFunctors

/-!
概要：二回の一頂点延長を、二次数先の標準単体として正規化する。
方針：二つの標準 join 同型を合成し、元の全形状への包含を頂点で検出する。
規約：初期の奇数次数にも使える。使われ方：二表示の可算全比較の標準単体による貼合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 二つの追加頂点を持つ全形状を二次数先の標準単体へ写す指定同型。 -/
def doubleConeSimplexIso (n : ℕ) :
    join (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ≅ Δ[n + 2] :=
  joinIso (joinStdSimplexIso n 0) (Iso.refl _) ≪≫ joinStdSimplexIso (n + 1) 0

/-- 二つの追加頂点を除く全制限は、元の同じ前置標準単体への包含である。 -/
lemma doubleConeSimplexIso_prefix (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ joinInl (join Δ[n] Δ[0]) Δ[0] ≫
      (doubleConeSimplexIso n).hom = simplexPrefix (by omega : n ≤ n + 2) := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
