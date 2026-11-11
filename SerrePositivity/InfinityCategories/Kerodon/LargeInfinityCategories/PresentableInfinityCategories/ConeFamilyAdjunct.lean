module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeFunctorCounitPrism
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctParameterNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の全錐族から、定値図式の右随伴への比較射を構成する。
方針：全錐円柱の両端を厳密に照合し、随伴の全パラメータ Hom 対応で転置する。
規約：頂点ごとの独立な比較を選ばず、全関手圏の一つの射を使う。
使われ方：極限錐族の頂点関手と極限関手の全自然な比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全錐円柱はパラメータの前合成と厳密に可換。
方針：uncurry し、三座標の並べ替えと評価の自然性を使う。
規約：パラメータに quasicategory 性は不要。
使われ方：比較射の族制限との整合性。 -/
lemma coneFunctorCounitPrism_precomp {K A B X : SSet.{u}}
    (i : A ⟶ B) (s : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism (i ≫ s) := by
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism,
    uncurry_curry, uncurry_curry, uncurry_natural_left]
  have hr : (K ◁ (i ▷ (Δ[1] : SSet.{u}))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeUnitReorder K B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeUnitReorder K A ≫ ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) := rfl
  rw [← Category.assoc, ← Category.assoc, hr]
  simp only [Category.assoc, whisker_exchange]

/-- 概要：全錐族の頂点と図式を厳密な両端とする全ホモトピー。
方針：全円柱の両端公式を同じ関手へ照合する。
規約：始域の quasicategory 性を要求しない。
使われ方：前合成と整合する比較射の代表。 -/
def coneFunctorCounitHomotopy {K A X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    SSet.Homotopy ((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) (s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism s
  h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism_zero s).trans (Category.assoc _ _ _).symm
  h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism_one s
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：全錐族の定値頂点から図式への、元の全関手圏内の射。
方針：全錐円柱の代表辺を取り、始端と終端の厳密な等式で輸送する。
規約：錐の極限性をこの定義に含めない。
使われ方：随伴の Hom 対応に渡す指定射。 -/
def coneFunctorCounitHom {K A X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) (s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (coneFunctorCounitHomotopy s))

/-- 概要：全錐族の指定射は任意のパラメータ制限と整合する。
方針：円柱の前合成公式を、元の代表辺の類へ移す。
規約：同じ射の類そのものの等式を結論する。
使われ方：随伴による比較の局所成分の回収。 -/
lemma coneFunctorCounitHom_precomp {K A B X : SSet.{u}}
    (i : A ⟶ B) (s : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    coneFunctorCounitHom (i ≫ s) =
      (hoFunctor.map ((pre i).app ((ihom K).obj X))).toFunctor.map
        (coneFunctorCounitHom s) := by
  unfold coneFunctorCounitHom
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  congr 1
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism (i ≫ s))) =
    SSet.yonedaEquiv (curry ((i ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitPrism s))
  rw [coneFunctorCounitPrism_precomp]

/-- 概要：全錐族の頂点から定値図式の右随伴への全自然な比較射。
方針：元の円柱の Hom 類を、同じパラメータ上の随伴 Hom 対応で転置する。
規約：錐の極限性と比較の可逆性は別途証明する。
使われ方：任意の極限錐族の指定右随伴への比較。 -/
def coneFamilyAdjunctHom {K A X : SSet.{u}} [Quasicategory A] [Quasicategory X]
    {R : (ihom K).obj X ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) R)
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K)))
      ((s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X) ≫ R) :=
  a.homEquiv _ _ (coneFunctorCounitHom s)

/-- 概要：随伴で得る全錐族の比較射はパラメータ制限に自然。
方針：指定射の前合成公式と随伴 Hom 対応の自然性を結合する。
規約：二つのパラメータは quasicategory とする。
使われ方：全比較射とその各点の比較の同一視。 -/
lemma coneFamilyAdjunctHom_precomp {K A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    {R : (ihom K).obj X ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) R)
    (i : A ⟶ B) (s : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X) :
    coneFamilyAdjunctHom a (i ≫ s) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map (coneFamilyAdjunctHom a s) := by
  unfold coneFamilyAdjunctHom
  rw [coneFunctorCounitHom_precomp]
  exact a.homEquiv_precomp i
    (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K)))
    (s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X) (coneFunctorCounitHom s)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
