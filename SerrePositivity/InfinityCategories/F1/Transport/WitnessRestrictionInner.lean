module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessKan
public import SerrePositivity.InfinityCategories.F1.Transport.SquareLifting

/-!
概要：単射な底変換に対する表現の選択空間の制限の内ホーン持ち上げ。
方針：周囲の四角形を持ち上げ、ホーンに含まれる全頂点の表現条件を回収する。
規約：一次の可逆な辺の持ち上げと全ホーン充填は別に証明する必要がある。
使われ方：Kerodon Lemma 5.6.8.10、制限写像の inner fibration 部分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance witnessRestrictionPullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：表現の選択空間の包含は単射。
方針：全部分複体の包含の単射性を使う。
規約：底と全空間の quasicategory 性を要求しない。
使われ方：Kerodon §5.6.8、制限の持ち上げの等式を周囲の空間で検査する。 -/
instance transportWitnessSpaceι_mono {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] : Mono (transportWitnessSpaceι p) :=
  inferInstanceAs (Mono (fullSubcomplexOnVertices _ (IsTransportWitnessVertex p)).ι)

/-- 概要：単射な底の制限は transport witnesses の inner fibration を与える。
方針：周囲の四角形の内ホーンを持ち上げ、全頂点で表現条件を回収する。
規約：全ホーン持ち上げ性や可縮性はこの段階では主張しない。
使われ方：Kerodon Lemma 5.6.8.10、境界固定延長に必要な相対充填。 -/
instance transportWitnessRestriction_innerFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) [Mono g] :
    InnerFibration (transportWitnessRestriction p g) where
  mem := by
    intro T U i hi
    cases hi with
    | @intro n i h0 hn =>
      have := InnerFibration.mem (q := transportSquareRestriction p g) _
        (innerHornInclusions.intro i h0 hn)
      constructor
      intro a b sq
      let sq' : CommSq (a ≫ transportWitnessSpaceι p) (horn (n + 2) i).ι
          (transportSquareRestriction p g) (b ≫ transportWitnessSpaceι (pullback.snd p g)) := ⟨by
        rw [Category.assoc, ← transportWitnessRestriction_ι, ← Category.assoc,
          sq.w, Category.assoc]⟩
      have hv : ∀ v : (Δ[n + 2] : SSet.{u + 1}) _⦋0⦌,
          IsTransportWitnessVertex p (sq'.lift.app _ v) := by
        intro v
        let w : (horn (n + 2) i : SSet.{u + 1}) _⦋0⦌ := ⟨v, vertex_mem_horn n i v⟩
        have hw := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w) sq'.fac_left
        change sq'.lift.app _ v = (a.app _ w).val at hw
        rw [hw]
        exact fullSubcomplexOnVertices_vertex (a.app _ w)
      let L := fullSubcomplexLift (IsTransportWitnessVertex p) sq'.lift hv
      have hL : L ≫ transportWitnessSpaceι p = sq'.lift := fullSubcomplexLift_ι _ _ _
      refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
      · apply (cancel_mono (transportWitnessSpaceι p)).1
        rw [Category.assoc, hL]
        exact sq'.fac_left
      · apply (cancel_mono (transportWitnessSpaceι (pullback.snd p g))).1
        rw [Category.assoc, transportWitnessRestriction_ι, ← Category.assoc, hL]
        exact sq'.fac_right

end SerrePositivity.InfinityCategories
