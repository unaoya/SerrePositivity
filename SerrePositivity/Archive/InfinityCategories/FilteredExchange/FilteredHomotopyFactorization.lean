module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredRelativeFactorization
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：filtered 余極限内の有限形状からのホモトピーは、一つの後続段で両端を保って実現できる。
方針：有限な円柱と二つの端点の包含に相対因子分解を適用する。
規約：元の二つの射と元の段からの射を厳密に保持する。
使われ方：空間の filtered 余極限における有限写像の同型類の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限形状からの二射の余極限内のホモトピーは後続段で実現できる。
方針：円柱への二端点の包含を使い、元のホモトピーの射全体を因子分解する。
規約：図式の値の Kan 性は不要。使われ方：ホモトピーが成立する有限な段の選択。 -/
lemma exists_homotopy_at_stage_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {K : SSet.{u}} [K.Finite] (j : I) (f g : K ⟶ F.obj j)
    (H : SSet.Homotopy (f ≫ c.ι.app j) (g ≫ c.ι.app j)) :
    ∃ (k : I) (v : j ⟶ k), Nonempty (SSet.Homotopy (f ≫ F.map v) (g ≫ F.map v)) := by
  let i : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) := coprod.desc SSet.ι₀ SSet.ι₁
  have hi : coprod.desc f g ≫ c.ι.app j = i ≫ H.h := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc, H.h₀]
    · rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc, H.h₁]
  obtain ⟨k, v, h, hh, _⟩ := finite_relative_factorization_of_filtered_isColimit hc
    i j (coprod.desc f g) H.h hi
  refine ⟨k, v, ⟨{ h := h, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩⟩
  · change SSet.ι₀ ≫ h = f ≫ F.map v
    have he := congrArg (fun t ↦ (coprod.inl : K ⟶ K ⨿ K) ≫ t) hh
    simpa only [i, ← Category.assoc, coprod.inl_desc] using he
  · change SSet.ι₁ ≫ h = g ≫ F.map v
    have he := congrArg (fun t ↦ (coprod.inr : K ⟶ K ⨿ K) ≫ t) hh
    simpa only [i, ← Category.assoc, coprod.inr_desc] using he
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.F2
