module
public import SerrePositivity.KST.SConstruction.ExactMaps
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily

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
def mapJoinCocone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCocone p) :
    JoinCocone (p ≫ f) := ⟨c.val ≫ f, by rw [← Category.assoc, c.property]⟩

/-- 概要：任意の図式の coslice の後合成は trivial Kan fibration を保つ。
方針：coslice の境界を join の単射に沿って同時に持ち上げる。
規約：図式の形状 K は任意。使われ方：余極限性の保存と反映。 -/
instance sliceUnderPostcomp_of_trivialKanFibration {K E B : SSet.{u}}
    (p : K ⟶ E) (q : E ⟶ B) [TrivialKanFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let i := joinMap (𝟙 K) (boundary n).ι
  have hm : Mono i := joinMap_mono _ _
  have := TrivialKanFibration.mem (p := q) i hm
  have hw := congrArg (fun F => sliceUnderUncurry F) sq.w
  rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hw
  have s : CommSq (sliceUnderUncurry a) i q (sliceUnderUncurry b) := ⟨hw⟩
  have hK : joinInl K (Δ[n] : SSet.{u}) ≫ s.lift = p := by
    have h := congrArg (fun F => joinInl K (boundary n : SSet.{u}) ≫ F) s.fac_left
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry s.lift hK, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact s.fac_left
  · apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact s.fac_right

/-- 概要：trivial Kan fibration は任意の余極限錐を保存し反映する。
方針：coslice の後合成の同値による始対象性の判定を使う。
規約：形状 K は任意。使われ方：S_n の第一行制限の普遍性。 -/
lemma isColimitCone_iff_mapJoinCocone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    {p : K ⟶ E} (c : JoinCocone p) : IsColimitCone c ↔ IsColimitCone (mapJoinCocone q c) :=
  (qCatEquivalenceOfTrivialKanFibration (sliceUnderPostcomp p q)).isInitialVertex_iff c

/-- 概要：trivial Kan fibration は零頂点を保存し反映する。
方針：同値による始対象性と終対象性の保存・反映を組み合わせる。
規約：両端は quasicategory。使われ方：安定性の零角の輸送。 -/
lemma isZeroVertex_iff_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) [TrivialKanFibration q] (z : E _⦋0⦌) :
    IsZeroVertex z ↔ IsZeroVertex (q.app (Opposite.op ⦋0⦌) z) :=
  and_congr ((qCatEquivalenceOfTrivialKanFibration q).isInitialVertex_iff z)
    ((qCatEquivalenceOfTrivialKanFibration q).isTerminalVertex_iff z)

/-- 概要：trivial Kan fibration は押し出し正方形を保存し反映する。
方針：span の余錐への変換と余極限性の保存・反映を使う。
規約：実際の単体的正方形。使われ方：S 構成の保存条件の輸送。 -/
lemma isPushoutSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : IsPushoutSquare F ↔ IsPushoutSquare (F ≫ q) := by
  have h := isColimitCone_iff_mapJoinCocone_of_trivialKanFibration q (pushoutCocone F)
  apply h.trans
  apply isColimitCone_iff_of_val_eq
  exact Category.assoc _ _ _

/-- 概要：trivial Kan fibration は引き戻し正方形を保存し反映する。
方針：cospan の錐への変換と Core の極限性の保存・反映を使う。
規約：実際の単体的正方形。使われ方：安定性の輸送。 -/
lemma isPullbackSquare_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E) : IsPullbackSquare F ↔ IsPullbackSquare (F ≫ q) := by
  have h := isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (pullbackCone F)
  apply h.trans
  apply isLimitCone_iff_of_diagram_eq
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _

/-- 概要：trivial Kan fibration は S 構成の零対象と押し出しの保存条件を満たす。
方針：零対象と正方形の保存の方向をまとめる。
規約：両端の安定性は不要。使われ方：第一行制限の保存性。 -/
lemma preservesSConstructionData_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q] :
    PreservesSConstructionData q :=
  ⟨fun z hz => (isZeroVertex_iff_of_trivialKanFibration q z).1 hz,
    fun F hF => (isPushoutSquare_iff_postcomp_of_trivialKanFibration q F).1 hF⟩

/-- 概要：全次数の第一行制限は零対象と押し出しを保つ。
方針：L1b の trivial Kan fibration 性を適用する。
規約：C は安定な quasicategory。使われ方：S_n と第一行の普遍性の比較。 -/
lemma firstRowRestriction_preservesSConstructionData (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] : PreservesSConstructionData (firstRowRestriction n C) :=
  preservesSConstructionData_of_trivialKanFibration _

end SerrePositivity.KST.SConstruction
