module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：元の codiscrete ラベル写像を、指定した新しい頂点ラベルを持つ錐へ延長する。
方針：join の零単体の左右を分け、既存の codiscrete nerve の頂点による構成を適用する。
規約：元の底上の写像と右頂点の写像を厳密に保つ。
使われ方：κ-small な部分複体の錐を未使用ラベルで単射に埋め込む構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K : SSet.{u}} {T : Type u}

/-- 元の頂点ラベルと指定した右頂点ラベルをまとめた同じ錐の頂点関数。 -/
def coneVertexLabels (f : K _⦋0⦌ → T) (a : T) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋0⦌ → T := by
  intro s
  exact if h : s.1.val = 0 then a else
    f (cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) (by
      have hi : s.1.val < 2 := s.1.isLt
      omega : s.1.val = 1)) s.2.1)

/-- 元のラベル写像を、指定した頂点ラベルを持つ同じ錐へ延長する。 -/
def codiscreteConeLabelMap (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ nerve (Codiscrete T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap (coneVertexLabels (fun x => (nerveEquiv (f.app _ x)).as) a)

/-- 同じ錐のラベル写像は、元の底のラベル写像に厳密に制限する。 -/
lemma codiscreteConeLabelMap_inl (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ codiscreteConeLabelMap f a = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
  intro x
  change (nerveEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap _).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ x))).as = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex]
  rfl

/-- 同じ錐の右頂点の像は指定した同じラベル。 -/
lemma codiscreteConeLabelMap_inr (f : K ⟶ nerve (Codiscrete T)) (a : T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ codiscreteConeLabelMap f a =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Codiscrete.mk a)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerve_hom_ext
  intro x
  change (nerveEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap _).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app _ x))).as = a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.codiscreteNerveMap_vertex]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
