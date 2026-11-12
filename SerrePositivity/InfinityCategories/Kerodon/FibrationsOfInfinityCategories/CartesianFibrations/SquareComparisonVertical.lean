module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.SquareComparison

/-!
概要：縦に貼り合わせた可換四角形の比較射を pullback で分解する。
方針：各比較射の pullback の二成分を明示して、普遍性で同定する。
規約：単体集合や射の充填性は定義に不要。
使われ方：合成した射影と中間の射影に関する cartesian 性の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：上の四角形の比較の標的から縦合成の比較の標的への射。
方針：第一成分を保ち、第二成分を下の四角形の左射で写す。
規約：四角形を上下の順で指定する。
使われ方：縦合成の比較の因子分解。 -/
def squareComparisonVerticalMap {A₀ A₁ B₀ B₁ C₀ C₁ : SSet.{u}}
    {f : A₀ ⟶ A₁} {p : A₀ ⟶ B₀} {q : A₁ ⟶ B₁} {h : B₀ ⟶ B₁}
    {r : B₀ ⟶ C₀} {s : B₁ ⟶ C₁} {k : C₀ ⟶ C₁}
    (_sq₁ : CommSq f p q h) (sq₂ : CommSq h r s k) :
    pullback q h ⟶ pullback (q ≫ s) k :=
  pullback.lift (pullback.fst q h) (pullback.snd q h ≫ r) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, sq₂.w, ← Category.assoc])

/-- 概要：縦合成の比較の標的から下の四角形の比較の標的への射。
方針：第一成分を中間の右射で写し、第二成分を保つ。
規約：上の四角形の右射 q を明示する。
使われ方：比較の因子分解を表す pullback の下の底変換。 -/
def squareComparisonVerticalBase {A₁ B₁ C₀ C₁ : SSet.{u}}
    (q : A₁ ⟶ B₁) (s : B₁ ⟶ C₁) (k : C₀ ⟶ C₁) :
    pullback (q ≫ s) k ⟶ pullback s k :=
  pullback.lift (pullback.fst (q ≫ s) k ≫ q) (pullback.snd (q ≫ s) k) (by
    rw [Category.assoc, pullback.condition])

/-- 概要：縦合成の比較の因子分解の後半は下の比較の pullback。
方針：両成分で一致を検査し、指定された対の第一成分と中間の底を組にする。
規約：上の四角形や下の四角形の fibration 性は不要。
使われ方：下の比較が自明 Kan fibration の場合の移送。 -/
lemma squareComparisonVertical_isPullback {A₀ A₁ B₀ B₁ C₀ C₁ : SSet.{u}}
    {f : A₀ ⟶ A₁} {p : A₀ ⟶ B₀} {q : A₁ ⟶ B₁} {h : B₀ ⟶ B₁}
    {r : B₀ ⟶ C₀} {s : B₁ ⟶ C₁} {k : C₀ ⟶ C₁}
    (sq₁ : CommSq f p q h) (sq₂ : CommSq h r s k) :
    IsPullback (squareComparisonVerticalMap sq₁ sq₂) (pullback.snd q h)
      (squareComparisonVerticalBase q s k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison sq₂) := by
  apply IsPullback.mk'
  · apply pullback.hom_ext
    · simp only [squareComparisonVerticalMap, squareComparisonVerticalBase,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact pullback.condition
    · simp only [squareComparisonVerticalMap, squareComparisonVerticalBase,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc, pullback.lift_snd]
  · intro T a b h₁ h₂
    apply pullback.hom_ext
    · have hx := h₁ =≫ pullback.fst (q ≫ s) k
      simpa only [squareComparisonVerticalMap, Category.assoc, pullback.lift_fst] using hx
    · exact h₂
  · intro T a b hab
    have hf : (a ≫ pullback.fst (q ≫ s) k) ≫ q = b ≫ h := by
      have hx := hab =≫ pullback.fst s k
      simpa only [squareComparisonVerticalBase, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
        pullback.lift_fst] using hx
    have hs : a ≫ pullback.snd (q ≫ s) k = b ≫ r := by
      have hx := hab =≫ pullback.snd s k
      simpa only [squareComparisonVerticalBase, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
        pullback.lift_snd] using hx
    refine ⟨pullback.lift (a ≫ pullback.fst (q ≫ s) k) b hf, ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [squareComparisonVerticalMap, Category.assoc, pullback.lift_fst]
    · simp only [squareComparisonVerticalMap, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
      exact hs.symm

/-- 概要：縦合成の比較は上の比較と底変換された下の比較の合成。
方針：pullback の二成分で一致を確認する。
規約：四角形の縦合成は上から下へ。
使われ方：合成の cartesian 性から中間の射に関する性質を取り出す。 -/
lemma squareComparisonVertical_factor {A₀ A₁ B₀ B₁ C₀ C₁ : SSet.{u}}
    {f : A₀ ⟶ A₁} {p : A₀ ⟶ B₀} {q : A₁ ⟶ B₁} {h : B₀ ⟶ B₁}
    {r : B₀ ⟶ C₀} {s : B₁ ⟶ C₁} {k : C₀ ⟶ C₁}
    (sq₁ : CommSq f p q h) (sq₂ : CommSq h r s k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison sq₁ ≫ squareComparisonVerticalMap sq₁ sq₂ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison (sq₁.vert_comp sq₂) := by
  apply pullback.hom_ext <;>
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, squareComparisonVerticalMap, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

/-- 概要：下の比較が自明 Kan fibration なら縦合成の因子もそうなる。
方針：比較射の pullback 表示に底変換の保存性を適用する。
規約：quasicategory 性や上の比較の充填性は不要。
使われ方：比較射の合成と同値の消去則を組み合わせる。 -/
lemma squareComparisonVerticalMap_trivialKanFibration {A₀ A₁ B₀ B₁ C₀ C₁ : SSet.{u}}
    {f : A₀ ⟶ A₁} {p : A₀ ⟶ B₀} {q : A₁ ⟶ B₁} {h : B₀ ⟶ B₁}
    {r : B₀ ⟶ C₀} {s : B₁ ⟶ C₁} {k : C₀ ⟶ C₁}
    (sq₁ : CommSq f p q h) (sq₂ : CommSq h r s k)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison sq₂)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (squareComparisonVerticalMap sq₁ sq₂) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (squareComparisonVertical_isPullback sq₁ sq₂).flip
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison sq₂))⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
