module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FixedInnerHornFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete

/-!
概要：全頂点であらかじめ選んだ内ホーン充填を、同じパラメーターの全族へ延長する。
方針：内ホーン制限の自明 Kan 持ち上げ性を、パラメーターの零骨格包含に適用する。
規約：全頂点での指定値と、元のホーン全族をいずれも厳密に保持する。
使われ方：Ind-S (9b) の有限 enriched 制御から任意パラメーターへの復元。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 各頂点で選んだ充填を厳密に保持し、同じ全ホーン族を延長する。 -/
lemma innerHornFamily_lift_with_vertices {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (i : Fin (n + 1)) (hi₀ : 0 < i) (hiₙ : i < Fin.last n)
    (K : SSet.{u}) (b : K ⟶ (ihom (horn n i : SSet.{u})).obj X)
    (x : K _⦋0⦌ → ((ihom (Δ[n] : SSet.{u})).obj X) _⦋0⦌)
    (hx : ∀ v, ((pre (horn n i).ι).app X).app (Opposite.op ⦋0⦌) (x v) =
      b.app (Opposite.op ⦋0⦌) v) :
    ∃ F : K ⟶ (ihom (Δ[n] : SSet.{u})).obj X,
      F ≫ (pre (horn n i).ι).app X = b ∧
        ∀ v, F.app (Opposite.op ⦋0⦌) v = x v := by
  let p := (pre (horn n i).ι).app X
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
    (innerAnodyneExtensions.horn_ι hi₀ hiₙ) X
  have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K) p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K) p b :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp p b x hx⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  intro v
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) v
  change sq.lift.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) 0 at hv
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hv

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
