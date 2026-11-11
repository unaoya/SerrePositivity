module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：simplicial replacement から weighted nerve への taut scaffold の射。
方針：始点の係数単体を初区間へ制限し、各頂点の係数値へ輸送する。
規約：ここでは単体集合の射と底上の可換性を構成する。
使われ方：Kerodon Construction 5.3.4.11（Tag 0373）、strict transport の復元を比較する射。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：始点の係数単体が定める初区間の重み付き図式。
方針：各初区間の包含で制限した後、底の始点から各頂点への射を適用する。
規約：図式の自然性は初区間の包含と係数関手の合成則から従う。
使われ方：Kerodon Construction 5.3.4.11（Tag 0373）、taut scaffold の単体ごとの値。 -/
@[kerodon 0373]
def tautScaffoldDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ s.1 ⋙ F where
  app i := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n
    (Nat.le_of_lt_succ i.isLt)) ≫ s.2 ≫ F.map (s.1.map (homOfLE (Fin.zero_le i)))
  naturality i j f := by
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫ s.2 ≫
          F.map (s.1.map (homOfLE _))) =
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ s.2 ≫
        F.map (s.1.map (homOfLE _))) ≫ F.map (s.1.map f)
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]
    simp only [Category.assoc]
    rw [← F.map_comp, ← s.1.map_comp]
    rfl

/-- 概要：simplicial replacement から weighted nerve への taut scaffold の射。
方針：始点から各初区間への輸送で作った図式を weighted nerve の単体とする。
規約：係数の Kan 性を仮定せず、面と退化に関する自然性を直接確認する。
使われ方：Kerodon Construction 5.3.4.11（Tag 0373）、二つの全空間を比較する共通の始域からの射。 -/
@[kerodon 0373]
def tautScaffold {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F where
  app _ := ↾fun s ↦ ⟨s.1, tautScaffoldDiagram F s⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val e.unop.len _) ≫
        (stdSimplex.map α.unop ≫ τ ≫ F.map (σ.map (homOfLE _))) ≫
          F.map (σ.map (homOfLE _)) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.unop.toOrderHom i).val d.unop.len _) ≫
          τ ≫ F.map (σ.map (homOfLE _))
    simp only [Category.assoc]
    rw [← F.map_comp, ← σ.map_comp]
    rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← F.map_comp, ← σ.map_comp]
    rfl

/-- 概要：taut scaffold は底の nerve 上の射。
方針：両射とも底の射列を保つことを各次数で確認する。
規約：射影は simplicial replacement と weighted nerve の標準の射影。
使われ方：Kerodon Remark 5.3.4.12（Tag 0374）、scaffold の底に関する可換性。 -/
@[kerodon 0374]
lemma tautScaffold_projection {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    tautScaffold F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
