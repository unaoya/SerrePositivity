module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorFamilyTranspose

/-!
概要：二変数の関手空間から curry した関手空間への射。
方針：評価を結合子で三変数に直し、二回 curry する。
規約：写像空間の単体集合全体に作用する。
使われ方：Kerodon §4.5.1（Tag 01DQ）、共同評価の関手同型を図式の族の関手同型へ移す。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：二変数の関手を curry する操作を関手空間の射にする。
方針：三変数の評価を二回 curry する。
規約：quasicategory 性は構成に不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、coherent な比較の全次数での転送。 -/
def functorSpaceCurryMap (A B X : SSet.{u}) :
    (ihom (A ⊗ B)).obj X ⟶ (ihom B).obj ((ihom A).obj X) :=
  curry (curry ((α_ A B ((ihom (A ⊗ B)).obj X)).inv ≫ (ihom.ev (A ⊗ B)).app X))

/-- 概要：関手空間の curry の頂点は元の射の curry を表す。
方針：各変数の内部 Hom の評価式を計算する。
規約：頂点の厳密な等式。
使われ方：Kerodon §4.5.1（Tag 01DQ）、curry した比較の端点の同定。 -/
lemma functorSpaceCurryMap_vertex {A B X : SSet.{u}} (f : A ⊗ B ⟶ X) :
    (functorSpaceCurryMap A B X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro b
  apply CategoryTheory.Functor.functorHom_ext
  intro m β
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：共同評価の関手同型は curry した図式の族の関手同型を誘導する。
方針：関手空間の curry で頂点同型を写し、端点の公式を使う。
規約：標的 X の quasicategory 性だけを要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、大域的な単位の共同評価から族への移行。 -/
noncomputable def FunctorIso.curry {A B X : SSet.{u}} [Quasicategory X]
    {f g : A ⊗ B ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (curry f) (curry g) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (functorSpaceCurryMap A B X)
  simpa only [functorSpaceCurryMap_vertex] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso (curry)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
