module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition

/-!
概要：相対関手空間の頂点として底上の射を表す。
方針：通常の関手頂点に底上の固定条件を添え、逆方向は内部 Hom の零単体の同値を使う。
規約：始域・終域・底の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の同値から実際の底上の射を取り出す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の射を相対関手空間の頂点にする。
方針：functorVertex に後合成の固定条件を添える。
規約：可換性の証明の選択には依存しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の目標となる相対関手の指定。 -/
def relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : A ⟶ E) (hf : f ≫ p = a) : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) 0
    rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]⟩

/-- 概要：相対関手空間の全ての頂点は厳密な底上の射から得られる。
方針：内部 Hom の頂点を通常の射で表し、固定条件を functorVertex の単射性で戻す。
規約：底上の可換性は厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の本質的全射性から比較射を選ぶ。 -/
lemma exists_relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) _⦋0⦌) :
    ∃ (f : A ⟶ E) (hf : f ≫ p = a), relativeFunctorVertex p a f hf = v := by
  obtain ⟨f, hv⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).surjective v.val
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = v.val at hv
  have hf : f ≫ p = a := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    change ((ihom A).map p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
    rw [hv]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using v.property
  refine ⟨f, hf, ?_⟩
  apply Subtype.ext
  exact hv

/-- 概要：底上の前合成は相対関手の頂点を射の合成の頂点へ写す。
方針：部分型の値で内部 Hom の前合成を計算する。
規約：底の可換性は底上の射から得る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手の同型を比較射の制限の同型へ移す。 -/
lemma relativeFunctorOverPre_vertex {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (g : b.left ⟶ E) (hg : g ≫ p = b.hom) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f).app (Opposite.op ⦋0⦌) (relativeFunctorVertex p b.hom g hg) =
      relativeFunctorVertex p a.hom (f.left ≫ g)
        (by rw [Category.assoc, hg, f.w]) := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
