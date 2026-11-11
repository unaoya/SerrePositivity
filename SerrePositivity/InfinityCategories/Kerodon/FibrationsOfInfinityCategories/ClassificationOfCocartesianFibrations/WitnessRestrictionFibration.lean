module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp

/-!
概要：単射に沿う表現空間の制限は Kan fibration。
方針：一次の辺の持ち上げと可逆な辺を含む外側ホーンの充填を組み合わせる。
規約：モデル構造の仮定を使わない。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、境界固定延長の相対充填。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：単射への表現の制限は左ホーンを持ち上げる。
方針：一次では辺の延長を、高次では内ホーンと可逆な先頭辺の充填を使う。
規約：表現の存在や選択空間の可縮性を要求しない。
使われ方：表現空間の制限の全ホーン持ち上げ性。 -/
instance transportWitnessRestriction_leftFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) where
  mem := by
    intro T U i hi
    cases hi with
    | @intro n i hi =>
      constructor
      intro a b sq
      let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g
      cases n with
      | zero =>
        have hi₀ : i = 0 := by fin_cases i <;> simp_all
        subst i
        let x := SSet.yonedaEquiv (horn.ι (0 : Fin 2) 1 (by decide) ≫ a)
        let s := SSet.yonedaEquiv b
        have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g)).δ 1 s = q.app _ x := by
          rw [← stdSimplex.yonedaEquiv_δ_comp,
            ← horn.ι_ι_assoc (0 : Fin 2) 1 (by decide), ← sq.w,
            ← Category.assoc, SSet.yonedaEquiv_comp]
        let e : Truncated.Edge
            (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g))) (q.app _ x)
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g)).δ 0 s) := ⟨s, ht, rfl⟩
        obtain ⟨F, hF₀, hFq⟩ :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdgeLifting.transportWitnessRestriction_liftEdge_source p g x (SSet.Edge.ofTruncated e)
        refine CommSq.HasLift.mk' { l := F, fac_left := ?_, fac_right := ?_ }
        · apply horn.hom_ext'
          intro j hj
          fin_cases j
          · exact (hj rfl).elim
          · rw [horn.ι_ι_assoc]
            change stdSimplex.δ 1 ≫ F = horn.ι (0 : Fin 2) 1 (by decide) ≫ a
            rw [hF₀]
            exact SSet.yonedaEquiv.symm_apply_apply _
        · exact hFq.trans (SSet.yonedaEquiv.symm_apply_apply _)
      | succ n =>
        by_cases hi₀ : i = 0
        · subst i
          have : IsGroupoid (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p)) :=
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid _
          have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
              (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))) :=
            IsGroupoid.all_isIso (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p)) _
          obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_initialHorn q n a b sq.w he
          exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }
        · have := InnerFibration.mem (q := q) _
            (innerHornInclusions.intro i (Fin.pos_iff_ne_zero.mpr hi₀) hi)
          exact CommSq.HasLift.mk'
            { l := sq.lift, fac_left := sq.fac_left, fac_right := sq.fac_right }

/-- 概要：単射への表現空間の制限は全てのホーンを持ち上げる。
方針：Kan 複体間の left fibration の全ホーン充填を適用する。
規約：モデル構造の instance を仮定しない。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） (1)。 -/
lemma transportWitnessRestriction_fibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration
