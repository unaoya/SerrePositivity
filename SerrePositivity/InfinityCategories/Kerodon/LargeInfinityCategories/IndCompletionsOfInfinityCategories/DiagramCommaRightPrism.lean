module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaPrismNaturality

/-!
概要：元の図式 comma の C 全族と全円柱を、右因子の図式形状上にそろえる。
方針：同じ内部 Hom の随伴と対称な因子交換を使う。
規約：旧族・元の D・試験族と図式形状の両制限を厳密に保持する。
使われ方：下方余錐と元の試験族から、一般の二段 slice 持ち上げを作る。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)
/-- 概要：元の C 側の全図式を、右因子の図式形状上の族として読む。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
def diagramCommaOriginalFamily : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj C :=
  (β_ T ((SSet.uliftFunctor.{u + 1, u}).obj K)).hom ≫
    uncurry (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso K C).hom)
/-- 概要：元の全変換の円柱を、右因子の図式形状へ移す。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
def diagramCommaRightPrism : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C :=
  (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T Δ[0]) ((SSet.uliftFunctor.{u + 1, u}).obj K)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism κ D q
/-- 概要：旧族側の全境界は元の C 全図式の Yoneda 像。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
lemma diagramCommaRightPrism_old :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      diagramCommaRightPrism κ D q = diagramCommaOriginalFamily κ D q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C := by
  rw [diagramCommaRightPrism, ← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_old, diagramCommaOriginalFamily, Category.assoc]
/-- 概要：終端側面は元の指定図式 D そのもの。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
lemma diagramCommaRightPrism_tip :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      diagramCommaRightPrism κ D q =
    snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ D := by
  rw [diagramCommaRightPrism, ← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_tip, ← Category.assoc, braiding_hom_fst]
/-- 概要：元の試験族の任意の制限を全円柱で保持する。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
lemma diagramCommaRightPrism_precomp {T₀ : SSet.{u + 1}} (g : T₀ ⟶ T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 (Δ[0] : SSet.{u + 1})) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      diagramCommaRightPrism κ D q = diagramCommaRightPrism κ D (g ≫ q) := by
  rw [diagramCommaRightPrism, diagramCommaRightPrism, ← Category.assoc,
    BraidedCategory.braiding_naturality_left, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_precomp]
/-- 概要：元の図式形状の任意の制限を全円柱で保持する。
方針：元の全円柱と因子交換。規約：全射の等号。使われ方：点追加の slice 補間。 -/
lemma diagramCommaRightPrism_restrict {J : SSet.{u}} (f : J ⟶ K) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map f) ≫
      diagramCommaRightPrism κ D q =
    diagramCommaRightPrism κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D)
      (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D f) := by
  rw [diagramCommaRightPrism, diagramCommaRightPrism, ← Category.assoc,
    BraidedCategory.braiding_naturality_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_restrict]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
