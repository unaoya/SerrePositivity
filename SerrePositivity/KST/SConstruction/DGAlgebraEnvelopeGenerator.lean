module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeGeneration
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraSmallPerfectGenerator

/-! # 実 dg 代数の自由代表による拡張小模型の生成
概要：D の実小自由生成元を、元の延長像を含む小模型の実自由代表へ移す。
方針：元の小代表の生成定理と H⁰ 比較を、既存の包絡模型の生成移送へ渡す。
規約：全 Perf の Small 性も生成性の追加仮定も使わない。使われ方：実 ⊙ の二生成条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B : Mon (Complex R))
  (J : Type v) [Small.{u} J] (X : J → PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B))
  (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B)

/-- 元の dg 代数の実自由代表が、元の実延長像を含む小模型の全 Perf を生成する。 -/
lemma dgAlgebraEnvelope_perfectOver_representable_eq :
    modulePerfectOver R (DGSmallPerfectEnvelope R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) J X)
      {dgSmallPerfectEnvelopeRepresentable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) J X d} =
    modulePerfect R (DGSmallPerfectEnvelope R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) J X) :=
  dgSmallPerfectEnvelope_perfectOver_representable_eq R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) J X
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraSmallPerfectGenerator R B d) d
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraSmallPerfectGenerator_generates R B d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraSmallPerfectGenerator_homotopyComparison R B d)

end SerrePositivity.KST.SConstruction
