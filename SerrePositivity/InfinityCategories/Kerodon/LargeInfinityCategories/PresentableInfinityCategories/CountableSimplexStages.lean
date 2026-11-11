module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableFiniteExhaustion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDomains

/-!
概要：可算形状の反対 transport 単体圏に最小所属段階の関手を与える。
方針：面を取ると所属段階が増えないことを射の単調性に使う。
規約：元の transport 単体圏と元の有限段階の包含を使う。
使われ方：可算列に沿う局所左 Kan のコンマ圏を有限段階へ比較する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：反対単体圏の対象を最小所属段階へ送る関手。
方針：要素の圏の射を単体の生成部分複体の包含に読み替える。
規約：可算順序圏を元の形状と同じ宇宙へ持ち上げる。
使われ方：保存余極限の局所左 Kan 合成の底関手。 -/
def countableSimplexStageFunctor (X : SSet.{u}) [Countable X.S] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory X)ᵒᵖ ⥤ ULift.{u} ℕ where
  obj s := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStage X (S.equivElements.symm s.unop.objDown))
  map f := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStage_monotone X
    ((S.le_iff_nonempty_hom _ _).2 ⟨f.unop.down⟩))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 概要：段階関手の上界条件は単体の有限段階への所属そのもの。
方針：最小所属段階の判定を単体圏の対象に適用する。
規約：ULift の値をそのまま比較する。使われ方：局所左 Kan 形状の対象の同定。 -/
lemma countableSimplexStageFunctor_le_iff (X : SSet.{u}) [Countable X.S]
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory X)ᵒᵖ) (n : ℕ) :
    (countableSimplexStageFunctor X).obj s ≤ ULift.up n ↔
      s.unop.objDown.val ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).obj s.unop.objDown.obj := by
  rw [show (countableSimplexStageFunctor X).obj s ≤ ULift.up n ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStage X (S.equivElements.symm s.unop.objDown) ≤ n from Iff.rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableSimplexStage_le_iff]
  exact Subcomplex.ofSimplex_le_iff _ _

/-- 概要：有限増大列を単体集合の圏の図式として公開する。
方針：単調写像を関手にして部分複体の包含関手と合成する。
規約：通常の可算順序圏を添字に取る。使われ方：元の形状の余極限表示。 -/
def countableFiniteStageDiagram (X : SSet.{u}) [Countable X.S] : ℕ ⥤ SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage_monotone X).functor ⋙ Subcomplex.toSSetFunctor

/-- 概要：有限増大列から元の形状への余錐。
方針：各有限段階の包含を脚に取る。
規約：頂点は元の単体集合。使われ方：有限段階の合成の比較。 -/
def countableFiniteStageCocone (X : SSet.{u}) [Countable X.S] :
    Cocone (countableFiniteStageDiagram X) where
  pt := X
  ι := { app n := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage X n).ι }

/-- 概要：有限増大列の通常の余極限は元の形状である。
方針：段階の上限が全体であることと部分複体の filtered 余極限保存を使う。
規約：元の包含を脚に持つ余錐を証明する。
使われ方：有限形状の増大列と元の形状の比較。 -/
def countableFiniteStageCocone_isColimit (X : SSet.{u}) [Countable X.S] :
    IsColimit (countableFiniteStageCocone X) := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countableFiniteStage_monotone X).functor
  have h : IsLUB (Set.range f.obj) ⊤ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.iSup_countableFiniteStage X]
    exact isLUB_iSup
  let c := Preorder.colimitCoconeOfIsLUB f h
  have hc := isColimitOfPreserves Subcomplex.toSSetFunctor c.isColimit
  exact IsColimit.ofIsoColimit hc (Cocone.ext (Subcomplex.topIso X) (by intro n; rfl))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
