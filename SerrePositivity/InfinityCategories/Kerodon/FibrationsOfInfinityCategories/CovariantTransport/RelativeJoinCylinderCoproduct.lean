module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverCoproductComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEmpty
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
概要：構造射を保った coproduct 上の写像円柱比較の同値条件。
方針：単体集合の coproduct を Over 圏へ持ち上げ、初期対象を共有する比較を貼る。
規約：各 summand の構造射は任意、共通の終域 S を保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体と境界のセルの族。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：構造射の族の coproduct を Over 圏の cofan として表示する。
方針：構造射を Sigma.desc で貼り、各 coproduct 包含の底上の可換性を使う。
規約：基礎の単体集合は指定した単体集合の coproduct そのもの。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Mathlib のセルの族の構造射。 -/
noncomputable def relativeJoinOverSigmaCofan {J : Type u} {S : SSet.{u}}
    (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S) : Cofan (fun j ↦ Over.mk (f j)) :=
  Cofan.mk (Over.mk (Sigma.desc f)) (fun j ↦ Over.homMk (Sigma.ι X j) (Sigma.ι_comp_desc f j))

/-- 概要：構造射の族の指定した coproduct は Over 圏でも coproduct。
方針：基礎の coproduct の普遍性で射を貼り、底上の等式を包含で検査する。
規約：添字は宇宙 u。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各次元のセルの族の貼り合わせ。 -/
noncomputable def relativeJoinOverSigmaCofan_isColimit {J : Type u} {S : SSet.{u}}
    (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S) :
    IsColimit (relativeJoinOverSigmaCofan X f) where
  desc c := Over.homMk (Sigma.desc (fun j ↦ (c.ι.app ⟨j⟩).left)) (by
    change Sigma.desc (fun j ↦ (c.ι.app ⟨j⟩).left) ≫ c.pt.hom = Sigma.desc f
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact (c.ι.app ⟨j⟩).w)
  fac c j := by
    rcases j with ⟨j⟩
    apply Over.OverMorphism.ext
    exact Sigma.ι_comp_desc _ j
  uniq c m hm := by
    apply Over.OverMorphism.ext
    change m.left = Sigma.desc (fun j ↦ (c.ι.app ⟨j⟩).left)
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    exact congrArg (fun k ↦ k.left) (hm ⟨j⟩)

/-- 概要：Over 圏の初期対象の構造射の円柱比較は同値条件を満たす。
方針：忘却と各次数の評価が初期対象を保つことから空の始域の場合へ移す。
規約：S は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの族の比較の共通部分。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_initialOver (S : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (⊥_ (Over S)).hom) := by
  have hI : IsInitial ((⊥_ (Over S)).left) :=
    IsInitial.isInitialObj (Over.forget S) _ initialIsInitial
  let (n : SimplexCategoryᵒᵖ) : IsEmpty (((⊥_ (Over S)).left).obj n) :=
    (Types.initial_iff_empty _).mp
      ⟨IsInitial.isInitialObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n) _ hI⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_emptySource _

/-- 概要：各 summand の円柱比較の同値条件は構造射を保った coproduct でも成り立つ。
方針：Over 圏の cofan の比較に、初期対象からの wide pushout の貼り合わせを使う。
規約：各構造射の単射性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、同じ次元の境界と標準単体の族。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_sigma
    {J : Type u} {S : SSet.{u}} (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S)
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (f j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (Sigma.desc f)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_coproduct_cocone J
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparisonNat S) (fun j ↦ Over.mk (f j))
    (relativeJoinOverSigmaCofan X f) (relativeJoinOverSigmaCofan_isColimit X f)
    (isPrecompositionEquivalence_relativeJoinCylinderComparison_initialOver S) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
