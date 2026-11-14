module
public import SerrePositivity.KST.SConstruction.ExactMaps
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily

/-! # trivial Kan fibration による普遍性の保存と反映
概要：零対象と任意の余極限錐、押し出し・引き戻しを trivial Kan fibration で移す。
方針：coslice の後合成の持ち上げ性と、始対象性・終対象性の同値不変性を使う。
規約：Core・Stable の公開定義は変更しない。
使われ方：S_n の第一行制限を通じた安定性と保存性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：余錐を値域の射で後合成する。
方針：全余錐の射と固定図式を同じ射で写す。
規約：像の図式は p≫f。使われ方：余極限の保存の記述。 -/
def mapJoinCocone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ f) := ⟨c.val ≫ f, by rw [← Category.assoc, c.property]⟩

/-- 概要：任意の図式の coslice の後合成は trivial Kan fibration を保つ。
方針：coslice の境界を join の単射に沿って同時に持ち上げる。
規約：図式の形状 K は任意。使われ方：余極限性の保存と反映。 -/
instance sliceUnderPostcomp_of_trivialKanFibration {K E B : SSet.{u}}
    (p : K ⟶ E) (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (boundary n).ι
  have hm : Mono i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mono _ _
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) i hm
  have hw := congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry F) sq.w
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp] at hw
  have s : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a) i q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) := ⟨hw⟩
  have hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[n] : SSet.{u}) ≫ s.lift = p := by
    have h := congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (boundary n : SSet.{u}) ≫ F) s.fac_left
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at h
    exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry s.lift hK, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact s.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (p ≫ q)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact s.fac_right

/-- 概要：trivial Kan fibration は任意の余極限錐を保存し反映する。
方針：coslice の後合成の同値による始対象性の判定を使う。
規約：形状 K は任意。使われ方：S_n の第一行制限の普遍性。 -/
lemma isColimitCone_iff_mapJoinCocone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    {p : K ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (mapJoinCocone q c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q)).isInitialVertex_iff c

/-- 概要：trivial Kan fibration は零頂点を保存し反映する。
方針：同値による始対象性と終対象性の保存・反映を組み合わせる。
規約：両端は quasicategory。使われ方：安定性の零角の輸送。 -/
lemma isZeroVertex_iff_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q] (z : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.app (Opposite.op ⦋0⦌) z) :=
  and_congr ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration q).isInitialVertex_iff z)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration q).isTerminalVertex_iff z)

/-- 概要：trivial Kan fibration は押し出し正方形を保存し反映する。
方針：span の余錐への変換と余極限性の保存・反映を使う。
規約：実際の単体的正方形。使われ方：S 構成の保存条件の輸送。 -/
lemma isPushoutSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ q) := by
  have h := isColimitCone_iff_mapJoinCocone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
  apply h.trans
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq
  exact Category.assoc _ _ _

/-- 概要：trivial Kan fibration は引き戻し正方形を保存し反映する。
方針：cospan の錐への変換と Core の極限性の保存・反映を使う。
規約：実際の単体的正方形。使われ方：安定性の輸送。 -/
lemma isPullbackSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
  apply h.trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _

/-- 概要：trivial Kan fibration は S 構成の零対象と押し出しの保存条件を満たす。
方針：零対象と正方形の保存の方向をまとめる。
規約：両端の安定性は不要。使われ方：第一行制限の保存性。 -/
lemma preservesSConstructionData_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q] :
    PreservesSConstructionData q :=
  ⟨fun z hz => (isZeroVertex_iff_of_trivialKanFibration q z).1 hz,
    fun F hF => (isPushoutSquare_iff_postcomp_of_trivialKanFibration q F).1 hF⟩

/-- 概要：全次数の第一行制限は零対象と押し出しを保つ。
方針：L1b の trivial Kan fibration 性を適用する。
規約：C は安定な quasicategory。使われ方：S_n と第一行の普遍性の比較。 -/
lemma firstRowRestriction_preservesSConstructionData (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : PreservesSConstructionData (firstRowRestriction n C) :=
  preservesSConstructionData_of_trivialKanFibration _

end SerrePositivity.KST.SConstruction
