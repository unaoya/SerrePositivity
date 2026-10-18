module

public import SerrePositivity.InfinityCategories.F1B.IntervalFamilyClasses
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.PointwiseUnitComparison

/-!
概要：各点の写像空間の同値から定値関手間のパラメータ付き Hom 全単射を得る。
方針：族の代表を取り、実際のホモトピー逆の両合成を Hom の等式へ移す。
規約：非定値関手間の全単射をここから直接主張しない。
使われ方：B1 の左三角恒等式の各点での一意性を供給する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間のホモトピー同値を表す族の Hom 写像は全単射。
方針：代表族を取り、ホモトピー逆の両合成を使って単射性と全射性を証明する。
規約：パラメータ A は任意。両端の関手は定値。
使われ方：標準単位比較の各点の同値性を h Fun の一意性へ移す。 -/
lemma intervalFamilyComparison_bijective {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : intervalMappingSpace x₀ x₁ ⟶ intervalMappingSpace y₀ y₁)
    (hq : IsSimplicialHomotopyEquivalence q)
    (Φ : ConstantFunctorHom A X x₀ x₁ → ConstantFunctorHom A Y y₀ y₁)
    (hΦ : ∀ f : A ⟶ intervalMappingSpace x₀ x₁,
      Φ (intervalFamilyHom f) = intervalFamilyHom (f ≫ q)) : Function.Bijective Φ := by
  obtain ⟨r, ⟨H⟩, ⟨K⟩⟩ := hq
  have hH (f : A ⟶ intervalMappingSpace x₀ x₁) :
      intervalFamilyHom ((f ≫ q) ≫ r) = intervalFamilyHom f := by
    have h := functorHomotopyPrecomp H f
    have h' : SSet.Homotopy ((f ≫ q) ≫ r) f := by
      simpa only [Category.assoc, Category.comp_id] using h
    exact intervalFamilyHom_eq_of_homotopy h'
  have hK (g : A ⟶ intervalMappingSpace y₀ y₁) :
      intervalFamilyHom ((g ≫ r) ≫ q) = intervalFamilyHom g := by
    have h := functorHomotopyPrecomp K g
    have h' : SSet.Homotopy ((g ≫ r) ≫ q) g := by
      simpa only [Category.assoc, Category.comp_id] using h
    exact intervalFamilyHom_eq_of_homotopy h'
  constructor
  · intro α β h
    obtain ⟨f, rfl⟩ := intervalFamilyHom_surjective A X x₀ x₁ α
    obtain ⟨g, rfl⟩ := intervalFamilyHom_surjective A X x₀ x₁ β
    rw [hΦ, hΦ] at h
    obtain ⟨L⟩ := intervalFamilyHom_eq_iff_homotopy.mp h
    have hfg := intervalFamilyHom_eq_of_homotopy (functorHomotopyPostcomp L r)
    exact (hH f).symm.trans (hfg.trans (hH g))
  · intro β
    obtain ⟨g, rfl⟩ := intervalFamilyHom_surjective A Y y₀ y₁ β
    refine ⟨intervalFamilyHom (g ≫ r), ?_⟩
    rw [hΦ]
    exact hK g

/-- 概要：各点の単位比較条件は任意のパラメータの定値関手間の単位 Hom 比較を全単射にする。
方針：区間模型へ同値性を移し、族の単位公式を一般の全単射判定へ渡す。
規約：非定値関手に関する十分条件で各点の条件を置き換えていない。
使われ方：左三角恒等式の各点での一意性。 -/
lemma UnitMappingSpaceCondition.constantUnitHomMap_bijective
    {A X Y : SSet.{u}} [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Function.Bijective (constantUnitHomMap η A x y) := by
  apply intervalFamilyComparison_bijective (unitIntervalMap η x y)
    ((unitMappingSpaceCondition_iff_interval η).mp hη x y)
  intro f
  exact (unitIntervalMap_family η x y f).symm

end SerrePositivity.InfinityCategories
