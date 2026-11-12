module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaRelativeInitial
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeInitialHomotopy

/-!
概要：単位切断の相対始点境界充填から自然な余単位候補を構成する。
方針：comma 内で G に沿った単位切断を恒等矢印の族へ結び、標的へ射影する。
規約：相対充填を直接受け取る構成に加え、輸送を明示した中間版を残す。
追加の輸送仮定を使わない各点の条件からの公開定理は UnitCounitExistence に置く。
使われ方：B1 の指定単位の点ごとの普遍性から随伴を作る経路。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：G の各像の恒等矢印からなる comma の族。
方針：時間に定値なホモトピーを comma への持ち上げへ渡す。
規約：標的の関手は恒等関手、始域の関手は G。
使われ方：余単位候補を得る比較の終域。 -/
noncomputable def unitCommaIdentityFamily {X Y : SSet.{u}} (G : Y ⟶ X) :
    Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G G (𝟙 Y)
    { h := fst Y (Δ[1] : SSet.{u}) ≫ G
      h₀ := by simp
      h₁ := by simp
      rel := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro a
        exact False.elim a.1.property }

/-- 概要：恒等矢印の族の始域は G。
方針：comma の持ち上げの始域公式。
規約：厳密な等式。
使われ方：比較を同じ基底上に置く。 -/
lemma unitCommaIdentityFamily_source {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitCommaIdentityFamily G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = G :=
  by
    unfold unitCommaIdentityFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source _ _ _ _

/-- 概要：恒等矢印の族の標的は恒等関手。
方針：comma の持ち上げの標的公式。
規約：厳密な等式。
使われ方：射影したホモトピーの終点の認識。 -/
lemma unitCommaIdentityFamily_target {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitCommaIdentityFamily G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = 𝟙 Y :=
  by
    unfold unitCommaIdentityFamily
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target _ _ _ _

/-- 概要：相対始対象の単位切断から恒等矢印の族への基底を固定したホモトピーがある。
方針：点ごとの相対始点境界充填を G に沿って制限し、族への射の存在を適用する。
規約：相対始点境界充填を明示的に仮定する。四辺の端点だけから構成しない。
使われ方：余単位と単位の整合性を保持する comma 内の比較。 -/
lemma exists_unitCommaCounitComparison_of_relativeInitial
    {X Y : SSet.{u}} [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x)) :
    ∃ H : SSet.Homotopy (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) (unitCommaIdentityFamily G),
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = fst Y (Δ[1] : SSet.{u}) ≫ G := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_homotopy_over_of_pointwise_initialBoundaryLifting
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) (unitCommaIdentityFamily G)
    (fun y ↦ hη (G.app (Opposite.op ⦋0⦌) y)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_source, Category.comp_id,
        unitCommaIdentityFamily_source])
  refine ⟨H, ?_⟩
  simpa only [← Category.assoc, unitCommaIdentityFamily_source] using hH

/-- 概要：相対始対象の単位切断は自然な余単位候補を持つ。
方針：comma 内の比較を Y 値の標的へ射影する。
規約：三角恒等式はまだ結論しない。相対始点境界充填からの構成段階である。
使われ方：B1 の余単位の実際のホモトピー代表。 -/
lemma exists_unitCommaCounitHomotopy_of_relativeInitial
    {X Y : SSet.{u}} [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x)) :
    Nonempty (SSet.Homotopy (G ≫ F) (𝟙 Y)) := by
  obtain ⟨H, _⟩ := exists_unitCommaCounitComparison_of_relativeInitial η hη
  exact ⟨{ h := H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G
           h₀ := by
             rw [← Category.assoc, H.h₀, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_target]
             rfl
           h₁ := by
             rw [← Category.assoc, H.h₁, unitCommaIdentityFamily_target]
             rfl
           rel := by
             apply SSet.hom_ext
             intro d
             apply ConcreteCategory.hom_ext
             intro a
             exact False.elim a.1.property }⟩

/-- 概要：単位の comma 始対象性と始域射影の輸送から自然な余単位候補が存在する。
方針：fiber 内の始対象性を相対境界充填へ移し、comma 内の族の比較を射影する。
規約：始域射影の輸送を仮定に残す。三角恒等式はこの補題には含めない。
使われ方：B1 の局所存在判定に必要な余単位構成の接続。 -/
lemma UnitCommaInitialCondition.exists_counitHomotopy_of_op_transport
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G))]
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η) : Nonempty (SSet.Homotopy (G ≫ F) (𝟙 Y)) :=
  exists_unitCommaCounitHomotopy_of_relativeInitial η
    hη.initialBoundaryLifting_of_op_transport

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
