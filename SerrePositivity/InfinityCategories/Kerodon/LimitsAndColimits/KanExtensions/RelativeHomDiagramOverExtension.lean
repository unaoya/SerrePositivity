module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomDiagramExtension
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionSquareRelativeExtension

/-!
概要：変動する添字の図式を、部分図式と標的の全図式を固定して内ホーンから延長する。
方針：逆像の自然性の引き戻し四角形に相対的な貼り合わせを適用する。
規約：標的の射に対する持ち上げ条件を明示する。
使われ方：全空間の相対比較の inner fibration 性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：内ホーンの逆像の図式を標的の全図式の上で延長できる。
方針：内ホーン逆像の包含の前合成同値と逆像の自然性の引き戻しを使う。
規約：添字間の射は単射で、二つの射影は cocartesian fibration。
使われ方：全空間の相対比較の内ホーン持ち上げ。 -/
lemma exists_kanRelativeHomDiagram_extension_over {C D E : SSet.{u}}
    {K L A B : Over C} (i : K ⟶ L) [Mono i.left]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration K.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration L.hom]
    (u : A ⟶ B) (hu : innerHornInclusions u.left) (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m → HasLiftingProperty m U)
    (F : pullback B.hom K.hom ⟶ D) (G : pullback A.hom L.hom ⟶ D)
    (H₀ : pullback B.hom L.hom ⟶ E)
    (hFG : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom).map u ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i A ≫ G)
    (hF : F ≫ U = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i B ≫ H₀)
    (hG : G ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom).map u ≫ H₀) :
    ∃ H : pullback B.hom L.hom ⟶ D,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i B ≫ H = F ∧ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom).map u ≫ H = G ∧
        H ≫ U = H₀ := by
  have hm : ∀ {X Y : SSet.{u}} (f : X ⟶ Y), innerHornInclusions f → Mono f := by
    intro X Y f hf
    cases hf
    infer_instance
  have : Mono u.left := hm u.left hu
  have : Mono u := (Over.forget C).mono_of_mono_map (show Mono u.left from inferInstance)
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_kanPrecompositionSquare_extension_over
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom).map u) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i A) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i B)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom).map u) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.overPullbackMap_naturality_isPullback i u)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence K.hom u hu)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence L.hom u hu)
    U hU F G H₀ hFG hF hG

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
