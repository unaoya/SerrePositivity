module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation

/-! # 自由 dg Hom の各次数の生成元による外延性

概要：自由 Hom の任意次数からの線形写像を、全 path summand 上で比較する。
方針：複体の直和の余極限を次数評価で保存し、余極限の Hom 外延性を使う。
規約：chain map 条件は要求しない。使われ方：厳密 dg 自然変換の斉次自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (O : Type v) [Small.{u} O]

/-- 自由 Hom の任意次数上の線形写像は、各 path の同じ次数への制限で決まる。 -/
lemma freeHomDegree_ext (K : FreeDGCategory.ComplexQuiver A O) (x y : O) (k : ℤ)
    {N : ModuleCat.{u} A}
    {f g : ((FreeDGCategory.homComplex A O K x y).X k) ⟶ N}
    (h : ∀ p, (FreeDGCategory.pathInclusion A O K x y p).f k ≫ f =
      (FreeDGCategory.pathInclusion A O K x y p).f k ≫ g) : f = g := by
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k)
    (colimit.isColimit (Discrete.functor
      (FreeDGCategory.pathTensor A O K (x := x) (y := y))))).hom_ext
  intro p
  exact h p.as

end SerrePositivity.InfinityCategories.Project.DerivedCategories
