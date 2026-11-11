module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
概要：filtered 余極限への有限な相対写像は一つの後続段で境界を保って実現できる。
方針：有限表示性で写像を一段へ下ろし、境界上の等式を共通の後続段で成立させる。
規約：通常の小圏による strict 図式の余極限余錐を扱う。
使われ方：有限なホモトピーの相対因子分解と compact 性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限な境界を指定した射は filtered 図式の一つの後続段で実現できる。
方針：写像と境界の二回の有限表示性を使い、指定された元の段からの射も保持する。
規約：図式の値の Kan 性は不要。使われ方：実際の有限ホモトピーの検出。 -/
lemma finite_relative_factorization_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {A B : SSet.{u}} [A.Finite] [B.Finite] (i : A ⟶ B)
    (j : I) (a : A ⟶ F.obj j) (b : B ⟶ c.pt) (h : a ≫ c.ι.app j = i ≫ b) :
    ∃ (k : I) (v : j ⟶ k) (g : B ⟶ F.obj k),
      i ≫ g = a ≫ F.map v ∧ g ≫ c.ι.app k = b := by
  obtain ⟨l, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc b
  obtain ⟨k, v, w, hw⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a (i ≫ g) (by
    rw [Category.assoc, hg]
    exact h)
  refine ⟨k, v, g ≫ F.map w, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans hw.symm
  · rw [Category.assoc, c.w w]
    exact hg

end SerrePositivity.InfinityCategories.Project.FilteredExchange
