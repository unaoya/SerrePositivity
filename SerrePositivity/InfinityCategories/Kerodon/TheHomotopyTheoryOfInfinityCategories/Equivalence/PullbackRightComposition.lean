module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：一方の因子の合成から誘導される引き戻しの比較。
方針：二段の引き戻しの普遍性で比較自体を引き戻しと示す。
規約：全て単体集合の通常の引き戻し。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path を用いた引き戻しの比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：右側の射の合成と可換な射から引き戻し間の比較を作る。
方針：第一射影を保ち第二射影に r を合成する。
規約：q=r≫p の等式を明示する。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path の解像の比較。 -/
noncomputable def pullbackMapRightOfComp {E B F T : SSet.{u}}
    (e : E ⟶ B) (p : F ⟶ B) (q : T ⟶ B) (r : T ⟶ F) (h : q = r ≫ p) :
    pullback e q ⟶ pullback e p :=
  pullback.lift (pullback.fst e q) (pullback.snd e q ≫ r) (by
    rw [Category.assoc, ← h, pullback.condition])

/-- 概要：合成からの引き戻し比較の第一射影は元の第一射影。
方針：lift の計算を使う。
規約：任意の合成の等式 h。
使われ方：Kerodon §4.5.3（Tag 032Y） の比較の検証。 -/
lemma pullbackMapRightOfComp_fst {E B F T : SSet.{u}}
    (e : E ⟶ B) (p : F ⟶ B) (q : T ⟶ B) (r : T ⟶ F) (h : q = r ≫ p) :
    pullbackMapRightOfComp e p q r h ≫ pullback.fst e p = pullback.fst e q :=
  pullback.lift_fst _ _ _

/-- 概要：合成からの引き戻し比較の第二射影は r との合成。
方針：lift の計算を使う。
規約：任意の合成の等式 h。
使われ方：Kerodon §4.5.3（Tag 032Y） の比較の検証。 -/
lemma pullbackMapRightOfComp_snd {E B F T : SSet.{u}}
    (e : E ⟶ B) (p : F ⟶ B) (q : T ⟶ B) (r : T ⟶ F) (h : q = r ≫ p) :
    pullbackMapRightOfComp e p q r h ≫ pullback.snd e p = pullback.snd e q ≫ r :=
  pullback.lift_snd _ _ _

/-- 概要：合成からの引き戻し比較は r の基底変換。
方針：二つの射影による外延性と入れ子の lift で普遍性を示す。
規約：q=r≫p。
使われ方：Kerodon §4.5.3（Tag 032Y） の全境界持ち上げの移送。 -/
lemma pullbackMapRightOfComp_isPullback {E B F T : SSet.{u}}
    (e : E ⟶ B) (p : F ⟶ B) (q : T ⟶ B) (r : T ⟶ F) (h : q = r ≫ p) :
    IsPullback (pullback.snd e q) (pullbackMapRightOfComp e p q r h) r (pullback.snd e p) := by
  refine IsPullback.mk' (pullbackMapRightOfComp_snd e p q r h).symm ?_ ?_
  · intro Z φ ψ h₀ h₁
    apply pullback.hom_ext
    · have he := congrArg (fun k ↦ k ≫ pullback.fst e p) h₁
      simpa only [Category.assoc, pullbackMapRightOfComp_fst] using he
    · exact h₀
  · intro Z a b hab
    have hw : (b ≫ pullback.fst e p) ≫ e = a ≫ q := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hab, Category.assoc, ← h]
    let F := pullback.lift (b ≫ pullback.fst e p) a hw
    refine ⟨F, pullback.lift_snd _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapRightOfComp_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackMapRightOfComp_snd, ← Category.assoc, pullback.lift_snd]
      exact hab

/-- 概要：r が全単射に対して持ち上がれば合成からの引き戻し比較も持ち上がる。
方針：比較が r の基底変換であることを使う。
規約：trivial Kan fibration の定義は既存の rlp。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path の解像。 -/
lemma trivialKanFibration_pullbackMapRightOfComp {E B F T : SSet.{u}}
    (e : E ⟶ B) (p : F ⟶ B) (q : T ⟶ B) (r : T ⟶ F) (h : q = r ≫ p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullbackMapRightOfComp e p q r h) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (pullbackMapRightOfComp_isPullback e p q r h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := r))⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
