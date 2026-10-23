module

public import SerrePositivity.InfinityCategories.F2.Ind.KappaRelativeFactorization
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallJoin
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
概要：通常の κ-filtered 余極限内の元の coslice 図式を、指定した終点図式を保って後続段へ下ろす。
方針：元の coslice 全体を join に展開し、右境界を固定した相対因子分解を使う。
規約：点ごとの射だけでなく全 join の等号を返す。使われ方：全空間比較の coslice 内の余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の coslice 全図式は、指定段での終点図式を保って一つの後続段へ因子分解する。 -/
lemma exists_coslice_join_at_stage {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I κ]
    {F : I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {K : SSet.{u}} (hK : IsKappaSmall κ K) (j : I) (g : K ⟶ F.obj j)
    (x : c.pt _⦋0⦌) (b : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (hb : g ≫ c.ι.app j = b ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x)) :
    ∃ (k : I) (v : j ⟶ k) (h : join (Δ[0] : SSet.{u}) K ⟶ F.obj k),
      joinInr Δ[0] K ≫ h = g ≫ F.map v ∧ h ≫ c.ι.app k = sliceUnderUncurry b := by
  have hκ : κ.IsRegular := Fact.out
  have hjoin : IsKappaSmall κ (join (Δ[0] : SSet.{u}) K) :=
    isKappaSmall_join hκ (isKappaSmall_of_finite hκ.aleph0_le _) hK
  exact kappaSmall_relative_factorization_of_isColimit hc hK hjoin (joinInr Δ[0] K)
    j g (sliceUnderUncurry b) (hb.trans (sliceUnderUncurry_projection b).symm)

end SerrePositivity.InfinityCategories.F2.Ind
