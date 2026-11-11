module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：可換四角形の相対比較写像とその充填の合成。
方針：引き戻しへの比較写像の trivial Kan fibration 性を二つの固定条件の充填に移す。
規約：四角形の横の合成は左から右。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、Proposition 5.2.5.1（Tag 01VU） の相対 coslice の合成。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：可換四角形から二つの射の引き戻しへの相対比較写像を作る。
方針：上と左の射を組にする。
規約：sq の等式は f ≫ q = p ≫ g。
使われ方：Kerodon Proposition 5.1.1.14（Tag 01TF）、相対 coslice の比較写像の共通形。 -/
noncomputable def squareComparison {E F B C : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g) : E ⟶ pullback q g :=
  pullback.lift f p sq.w

/-- 概要：相対比較写像の持ち上げは上と左の二つの図式を同時に固定する。
方針：引き戻しへの下の射を作り、単射に対する右持ち上げ性を使う。
規約：i は任意の単射。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、相対的な錐を段階的に延長する。 -/
lemma squareComparison_exists_lift {E F B C A D : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq)] (i : A ⟶ D) [Mono i]
    (a : A ⟶ E) (b : D ⟶ F) (c : D ⟶ B)
    (hab : a ≫ f = i ≫ b) (hac : a ≫ p = i ≫ c) (hbc : b ≫ q = c ≫ g) :
    ∃ l : D ⟶ E, i ≫ l = a ∧ l ≫ f = b ∧ l ≫ p = c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := squareComparison sq) i inferInstance
  let d := pullback.lift b c hbc
  have hs : CommSq a i (squareComparison sq) d := by
    constructor
    apply pullback.hom_ext
    · simpa only [squareComparison, d, Category.assoc, pullback.lift_fst] using hab
    · simpa only [squareComparison, d, Category.assoc, pullback.lift_snd] using hac
  refine ⟨hs.lift, hs.fac_left, ?_, ?_⟩
  · have h := congrArg (fun t ↦ t ≫ pullback.fst q g) hs.fac_right
    simpa only [squareComparison, d, Category.assoc, pullback.lift_fst] using h
  · have h := congrArg (fun t ↦ t ≫ pullback.snd q g) hs.fac_right
    simpa only [squareComparison, d, Category.assoc, pullback.lift_snd] using h

/-- 概要：横に並ぶ二つの相対比較写像が trivial Kan fibration なら合成四角形もそうなる。
方針：右の四角形で先に充填し、左の四角形でその充填を持ち上げる。
規約：quasicategory 性は不要。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、三角形から始点への相対制限の合成。 -/
lemma squareComparison_trivialKanFibration_horiz_comp
    {E₂ E₁ E₀ B₂ B₁ B₀ : SSet.{u}}
    {f : E₂ ⟶ E₁} {g : E₁ ⟶ E₀} {p₂ : E₂ ⟶ B₂} {p₁ : E₁ ⟶ B₁}
    {p₀ : E₀ ⟶ B₀} {b : B₂ ⟶ B₁} {c : B₁ ⟶ B₀}
    (sq₂ : CommSq f p₂ p₁ b) (sq₁ : CommSq g p₁ p₀ c)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq₂)]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq₁)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison (sq₂.horiz_comp sq₁)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a d hs
  let i := (boundary n).ι
  let x := d ≫ pullback.fst p₀ (b ≫ c)
  let y := d ≫ pullback.snd p₀ (b ≫ c)
  have hax : a ≫ (f ≫ g) = i ≫ x := by
    have h := congrArg (fun t ↦ t ≫ pullback.fst p₀ (b ≫ c)) hs.w
    simpa only [squareComparison, i, x, Category.assoc, pullback.lift_fst] using h
  have hay : a ≫ p₂ = i ≫ y := by
    have h := congrArg (fun t ↦ t ≫ pullback.snd p₀ (b ≫ c)) hs.w
    simpa only [squareComparison, i, y, Category.assoc, pullback.lift_snd] using h
  have hxy : x ≫ p₀ = (y ≫ b) ≫ c := by
    simp only [x, y, Category.assoc, pullback.condition]
  have haf : (a ≫ f) ≫ p₁ = i ≫ (y ≫ b) := by
    rw [Category.assoc, sq₂.w, ← Category.assoc, hay, Category.assoc]
  obtain ⟨l₁, hl₁, hl₁g, hl₁p⟩ :=
    squareComparison_exists_lift sq₁ i (a ≫ f) x (y ≫ b) hax haf hxy
  obtain ⟨l₂, hl₂, hl₂f, hl₂p⟩ :=
    squareComparison_exists_lift sq₂ i a l₁ y hl₁.symm hay hl₁p
  refine CommSq.HasLift.mk' {
    l := l₂
    fac_left := hl₂
    fac_right := ?_ }
  apply pullback.hom_ext
  · simpa only [squareComparison, Category.assoc, pullback.lift_fst] using
      (show l₂ ≫ (f ≫ g) = x by rw [← Category.assoc, hl₂f, hl₁g])
  · simpa only [squareComparison, Category.assoc, pullback.lift_snd] using hl₂p

/-- 概要：左の比較と合成比較が trivial Kan fibration なら、底の左射の同じ性質の下で右比較もそうなる。
方針：底と左の比較の切断で境界の図式を左へ移し、合成比較で充填する。
規約：横の左側の底の射 b にも trivial Kan fibration 性を要求する。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、長辺の coslice の相対的な充填性の消去。 -/
lemma squareComparison_trivialKanFibration_cancel_left
    {E₂ E₁ E₀ B₂ B₁ B₀ : SSet.{u}}
    {f : E₂ ⟶ E₁} {g : E₁ ⟶ E₀} {p₂ : E₂ ⟶ B₂} {p₁ : E₁ ⟶ B₁}
    {p₀ : E₀ ⟶ B₀} {b : B₂ ⟶ B₁} {c : B₁ ⟶ B₀}
    (sq₂ : CommSq f p₂ p₁ b) (sq₁ : CommSq g p₁ p₀ c)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq₂)]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison (sq₂.horiz_comp sq₁))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq₁) := by
  obtain ⟨s₂, hs₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (squareComparison sq₂)
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section b
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a d hs
  let i := (boundary n).ι
  let x := d ≫ pullback.fst p₀ c
  let y := d ≫ pullback.snd p₀ c
  let z := y ≫ t
  have hz : z ≫ b = y := by dsimp only [z]; rw [Category.assoc, ht, Category.comp_id]
  have hax : a ≫ g = i ≫ x := by
    have h := congrArg (fun k ↦ k ≫ pullback.fst p₀ c) hs.w
    simpa only [squareComparison, i, x, Category.assoc, pullback.lift_fst] using h
  have hay : a ≫ p₁ = i ≫ y := by
    have h := congrArg (fun k ↦ k ≫ pullback.snd p₀ c) hs.w
    simpa only [squareComparison, i, y, Category.assoc, pullback.lift_snd] using h
  have hxy : x ≫ p₀ = z ≫ (b ≫ c) := by
    rw [← Category.assoc, hz]
    simp only [x, y, Category.assoc, pullback.condition]
  let v := pullback.lift a (i ≫ z) (by rw [Category.assoc, hz]; exact hay)
  let a₂ := v ≫ s₂
  have ha₂ : a₂ ≫ squareComparison sq₂ = v := by
    dsimp only [a₂]
    rw [Category.assoc, hs₂, Category.comp_id]
  have ha₂f : a₂ ≫ f = a := by
    have h := congrArg (fun k ↦ k ≫ pullback.fst p₁ b) ha₂
    simpa only [squareComparison, v, Category.assoc, pullback.lift_fst] using h
  have ha₂p : a₂ ≫ p₂ = i ≫ z := by
    have h := congrArg (fun k ↦ k ≫ pullback.snd p₁ b) ha₂
    simpa only [squareComparison, v, Category.assoc, pullback.lift_snd] using h
  have ha₂g : a₂ ≫ (f ≫ g) = i ≫ x := by rw [← Category.assoc, ha₂f, hax]
  obtain ⟨l, hil, hlg, hlp⟩ :=
    squareComparison_exists_lift (sq₂.horiz_comp sq₁) i a₂ x z ha₂g ha₂p hxy
  refine CommSq.HasLift.mk' {
    l := l ≫ f
    fac_left := by rw [← Category.assoc, hil, ha₂f]
    fac_right := ?_ }
  apply pullback.hom_ext
  · simpa only [squareComparison, Category.assoc, pullback.lift_fst] using hlg
  · have h : (l ≫ f) ≫ p₁ = y := by
      rw [Category.assoc, sq₂.w, ← Category.assoc, hlp, hz]
    simpa only [squareComparison, Category.assoc, pullback.lift_snd] using h

/-- 概要：横の射を等しい表示に置き換えても相対比較写像の充填性は変わらない。
方針：二つの等式で置換し、可換性の証明の違いを証明無関係性で除く。
規約：縦の射と四隅の対象は固定する。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、coslice 制限の合成表示の正規化。 -/
lemma squareComparison_trivialKanFibration_congr {E F B C : SSet.{u}}
    {f f' : E ⟶ F} {p : E ⟶ B} {q : F ⟶ C} {g g' : B ⟶ C}
    (sq : CommSq f p q g) (sq' : CommSq f' p q g') (hf : f = f') (hg : g = g') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparison sq') := by
  subst f'
  subst g'
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
