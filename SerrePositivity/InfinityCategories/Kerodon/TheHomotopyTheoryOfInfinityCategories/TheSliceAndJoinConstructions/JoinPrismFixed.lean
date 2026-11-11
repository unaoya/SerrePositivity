module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：join の両因子上で定値な円柱は両端の関手の同型を与える。
方針：join の各頂点は片側の因子に属するため、各垂直辺は退化辺となる。
規約：標的だけを quasicategory とする。
使われ方：図式と頂点を固定した余錐の比較から余極限性を移す。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：join の各頂点は左右いずれかの因子から来る。
方針：零単体の切断が零か一であることを使う。
規約：両因子が空でも成立する。
使われ方：両因子の固定条件から全頂点の可逆性を導く。 -/
lemma join_vertex_cases (A B : SSet.{u}) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) _⦋0⦌) :
    (∃ a : A _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app (Opposite.op ⦋0⦌) a = x) ∨
      ∃ b : B _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app (Opposite.op ⦋0⦌) b = x := by
  rcases x with ⟨k, a, b⟩
  fin_cases k
  · cases a
    exact Or.inr ⟨b, rfl⟩
  · cases b
    exact Or.inl ⟨a, rfl⟩

/-- 概要：ある部分の像で定値な円柱は、その部分の各頂点で可逆な垂直辺を持つ。
方針：固定条件を頂点の定値辺で評価し退化辺へ同定する。
規約：部分への射 i は単射でなくてよい。
使われ方：join の左右の固定条件から関手同型を構成する。 -/
lemma prism_vertical_invertible_of_fixed_map {A B X : SSet.{u}}
    (P : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) (i : A ⟶ B) (q : A ⟶ X)
    (h : ((Δ[1] : SSet.{u}) ◁ i) ≫ P = snd Δ[1] A ≫ q) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (P.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) a) 1))) := by
  have he := congrArg (fun z : (Δ[1] : SSet.{u}) ⊗ A ⟶ X ↦
    z.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)) h
  change P.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), i.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)) = q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at he
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (P.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) a) 1))).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (q.app (Opposite.op ⦋0⦌) a)).edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hv).2
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (q.app (Opposite.op ⦋0⦌) a)))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：join の両因子で定値な円柱の両端は関手単体集合で同型。
方針：左右の因子による頂点の分割と点ごとの可逆性の判定を使う。
規約：q と r は一致しなくてよい。
使われ方：余錐の図式と頂点を固定した比較の普遍性の移送。 -/
def joinPrism_fixed_functorIso {A B X : SSet.{u}} [Quasicategory X]
    (P : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ X) (q : A ⟶ X) (r : B ⟶ X)
    (hA : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) ≫ P = snd Δ[1] A ≫ q)
    (hB : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) ≫ P = snd Δ[1] B ≫ r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ P) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ P) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy P
  intro x
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := join_vertex_cases A B x
  · exact prism_vertical_invertible_of_fixed_map P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) q hA a
  · exact prism_vertical_invertible_of_fixed_map P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) r hB b

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
