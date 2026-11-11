module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
概要：全部分複体の反転は反転した頂点条件の全部分複体と同型。
方針：零単体への全射を反転で置換し、各次数の同じ単体を対応させる。
規約：頂点条件の同型不変性や quasicategory 性は不要。
使われ方：元の相対右 Kan 関手の全部分圏を反転した左の全部分圏へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：全部分複体の反転の単体条件は反転した頂点条件に等しい。
方針：各頂点を指定する射を rev で置換し、二重反転を消す。
規約：任意の単体の次数と頂点条件を扱う。
使われ方：反転した全部分複体の同型の各成分の構成。 -/
lemma fullSubcomplex_op_mem_iff {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (n : SimplexCategoryᵒᵖ) (s : X.op.obj n) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).op.obj n ↔
      s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.op (fun x ↦ P (SSet.opObjEquiv x))).obj n := by
  constructor
  · intro hs v
    exact hs (SimplexCategory.rev.map v)
  · intro hs v
    have h := hs (SimplexCategory.rev.map v)
    change P (X.map (SimplexCategory.rev.map (SimplexCategory.rev.map v)).op
      s) at h
    rw [SimplexCategory.rev_map_rev_map] at h
    exact h

/-- 概要：全部分複体の反転は反転した頂点条件の全部分複体と同型。
方針：同じ単体を対応させ、全頂点条件だけを前の同値で移す。
規約：写像の単体の値を変更しない。
使われ方：右 Kan 条件を反転した左 Kan 条件へ頂点だけでなく全単体で移す。 -/
def fullSubcomplexOppositeIso {X : SSet.{u}} (P : X _⦋0⦌ → Prop) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}).op ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.op (fun x ↦ P (SSet.opObjEquiv x)) : SSet.{u}) where
  hom := {
    app n := ↾fun s ↦ ⟨s.val, (fullSubcomplex_op_mem_iff P n s.val).1 s.property⟩
    naturality := by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      rfl }
  inv := {
    app n := ↾fun s ↦ ⟨s.val, (fullSubcomplex_op_mem_iff P n s.val).2 s.property⟩
    naturality := by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact Subtype.ext rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact Subtype.ext rfl

/-- 概要：全部分複体の反転同型は元の反転した包含を保つ。
方針：同型の成分が単体の値を保つことを読む。
規約：全次数の単体写像の厳密な等式。
使われ方：元の相対制限と反転後の制限の可換正方形。 -/
lemma fullSubcomplexOppositeIso_hom_ι {X : SSet.{u}} (P : X _⦋0⦌ → Prop) :
    (fullSubcomplexOppositeIso P).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.op (fun x ↦ P (SSet.opObjEquiv x))).ι =
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι := rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
