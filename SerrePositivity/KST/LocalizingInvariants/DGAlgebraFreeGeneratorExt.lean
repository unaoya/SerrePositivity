module

public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation
public import SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraDerivedInfinity

/-!
概要：一対象 dg 代数への自由 dg 圏の生成辺データを、chain map の一致で判定する。
方針：標的の対象写像は一意であることを使い、実生成辺の等式を保持する。
規約：自由圏の普遍性は既存の実構成を使用。使われ方：cell 初期段の増大比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) (B : Mon (Complex R))
  (K : FreeDGCategory.ComplexQuiver R D)

lemma dgAlgebraGeneratorMap_ext
    {g h : FreeDGCategory.GeneratorMap R D (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) K}
    (hm : ∀ x y, g.map x y = h.map x y) : g = h := by
  cases g with
  | mk o f =>
    cases h with
    | mk o' f' =>
      have ho : o = o' := funext (fun x ↦ Subsingleton.elim _ _)
      subst o'
      congr 1
      funext x y
      exact hm x y

end SerrePositivity.KST.LocalizingInvariants
