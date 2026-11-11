module
public import SerrePositivity.KST.SConstruction.ObjectTriangulatedKZeroRelations
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FundamentalGroupoidComparison
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift

/-! # 元の object S から三角圏 K₀ の一対象亜群への関手
概要：元の辺の負の対象類を、ホモトピー圏と基本亜群からの実際の関手へ延長する。
方針：退化辺の零性と S₂ の加法関係を、辺と二単体の普遍性へ渡す。
規約：既存の BF 基本群表示の向きに合わせる。使われ方：K₀ 比較の逆写像の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 三角圏 K₀ の加法群を一対象亜群として表す。 -/
abbrev triangulatedKZeroDelooping (X : StableModel.{u}) :=
  SingleObj (Multiplicative (TriangulatedK0 (hoFunctor.obj X.carrier)))

/-- 元の object S の辺の負の対象類を、元のホモトピー圏からの関手へ降ろす。 -/
def objectTriangulatedFunctor (X : StableModel.{u}) :
    hoFunctor.obj (objectSConstruction X.carrier) ⥤ triangulatedKZeroDelooping X :=
  SSet.Truncated.HomotopyCategory.lift (fun _ => SingleObj.star _)
    (fun e => Multiplicative.ofAdd (-objectTriangulatedClass X e.edge))
    (by
      intro z
      change Multiplicative.ofAdd (-objectTriangulatedClass X
        ((objectSConstruction X.carrier).σ 0 z)) = 1
      rw [objectTriangulatedClass_degenerate, neg_zero]
      rfl)
    (by
      intro x y z e₀₁ e₁₂ e₀₂ r
      have h := objectTriangulatedClass_sTwo X r.simplex
      have h₀ : (objectSConstruction X.carrier).δ 0 r.simplex = e₁₂.edge := r.d₀
      have h₁ : (objectSConstruction X.carrier).δ 1 r.simplex = e₀₂.edge := r.d₁
      have h₂ : (objectSConstruction X.carrier).δ 2 r.simplex = e₀₁.edge := r.d₂
      rw [h₀, h₁, h₂] at h
      change Multiplicative.ofAdd (-objectTriangulatedClass X e₁₂.edge) *
          Multiplicative.ofAdd (-objectTriangulatedClass X e₀₁.edge) =
        Multiplicative.ofAdd (-objectTriangulatedClass X e₀₂.edge)
      apply Multiplicative.toAdd.injective
      change -objectTriangulatedClass X e₁₂.edge + -objectTriangulatedClass X e₀₁.edge =
        -objectTriangulatedClass X e₀₂.edge
      rw [← neg_add, add_comm]
      exact congrArg Neg.neg h.symm)

/-- 元の辺のホモトピー圏の類は、同じ辺の負の三角圏 K₀ 類へ写る。 -/
lemma objectTriangulatedFunctor_map_edge (X : StableModel.{u})
    {x y : (objectSConstruction X.carrier) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (objectSConstruction X.carrier)) x y) :
    (objectTriangulatedFunctor X).map (SSet.Truncated.HomotopyCategory.homMk e) =
      Multiplicative.ofAdd (-objectTriangulatedClass X e.edge) := by
  exact Category.id_comp (obj := triangulatedKZeroDelooping X)
    (Multiplicative.ofAdd (-objectTriangulatedClass X e.edge))

/-- 元の辺の負の対象類を、元の object S の基本亜群からの関手へ延長する。 -/
def objectTriangulatedGroupoidFunctor (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid (objectSConstruction X.carrier) ⥤
      triangulatedKZeroDelooping X := FreeGroupoid.lift (objectTriangulatedFunctor X)

/-- 元の object S から三角圏 K₀ の一対象亜群の nerve への実際の写像。 -/
def objectTriangulatedNerveMap (X : StableModel.{u}) :
    objectSConstruction X.carrier ⟶ nerve (AsSmall.{u} (triangulatedKZeroDelooping X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (objectTriangulatedFunctor X ⋙ AsSmall.up)

/-- 宇宙を揃えた三角圏 K₀ の一対象圏も亜群である。 -/
instance objectTriangulatedNerveTarget_isGroupoid (X : StableModel.{u}) :
    IsGroupoid (AsSmall.{u} (triangulatedKZeroDelooping X)) := by
  let e : triangulatedKZeroDelooping X ≌ AsSmall.{u} (triangulatedKZeroDelooping X) := AsSmall.equiv
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact isGroupoid_of_reflects_iso e.inverse

/-- 元の nerve 値写像を戻すと、元の辺の対象類の関手を厳密に回収する。 -/
lemma objectTriangulatedNerveMap_untranspose (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (objectTriangulatedNerveMap X) =
      objectTriangulatedFunctor X ⋙ AsSmall.up :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_transpose _

end SerrePositivity.KST.SConstruction
