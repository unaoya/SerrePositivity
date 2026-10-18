module

public import SerrePositivity.InfinityCategories.Core.RelativeEquivalencePathAt
public import SerrePositivity.InfinityCategories.Core.PullbackZigzag
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.InnerPullback

/-!
概要：可逆 path の相対持ち上げを持つ inner fibration に沿う同値の引き戻し。
方針：両端評価と相対 path の持ち上げによる共通の解像を使う。
規約：モデル構造を使わず、二つの trivial Kan fibration と切断で同値を示す。
使われ方：Kerodon §4.5.5 の categorical pushout の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：終点を指定した可逆 path の相対持ち上げを持つ inner fibration に沿って同値を引き戻せる。
方針：同値の path 置換と持ち上げられた path の共通の解像の全境界充填を使う。
規約：元の三対象は quasicategory、p は inner fibration と相対 path の持ち上げを持つ。
使われ方：Kerodon §4.5.5 の同値な図式の引き戻しの比較。 -/
lemma IsQCatEquivalence.pullback_snd_of_relativePath {E B F : SSet.{u}}
    [Quasicategory E] [Quasicategory B] [Quasicategory F] {e : E ⟶ B}
    (he : IsQCatEquivalence e) (p : F ⟶ B) [InnerFibration p]
    [TrivialKanFibration (relativeEquivalencePathMapAt p 1)] :
    IsQCatEquivalence (pullback.snd e p) := by
  have : InnerFibration (pullback.fst e p) :=
    ⟨innerFibrations.pullback_fst e p (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback e p) := quasicategory_of_innerFibration (pullback.fst e p)
  let q := equivalencePathEndpoint F 0 ≫ p
  let r := relativeEquivalencePathMapAt p 1
  let g := pullback.fst (equivalencePathEndpoint B 1) p ≫ equivalencePathEndpoint B 0
  have hq : q = r ≫ g := by
    symm
    change relativeEquivalencePathMapAt p 1 ≫
      (pullback.fst (equivalencePathEndpoint B 1) p ≫ equivalencePathEndpoint B 0) = _
    rw [← Category.assoc, relativeEquivalencePathMapAt_fst, equivalencePathMap_endpoint]
  let t := pullbackMapRightOfComp e p q (equivalencePathEndpoint F 0) rfl
  have ht : TrivialKanFibration t :=
    trivialKanFibration_pullbackMapRightOfComp e p q (equivalencePathEndpoint F 0) rfl
  have : Quasicategory (pullback e q) := quasicategory_of_innerFibration t
  let u := pullbackMapRightOfComp e g q r hq
  have hu : TrivialKanFibration u := trivialKanFibration_pullbackMapRightOfComp e g q r hq
  have hqe : TrivialKanFibration
      (pullback.fst (equivalencePathEndpoint B 0) e ≫ equivalencePathEndpoint B 1) :=
    he.equivalencePathReplacementMap_trivialKanFibration
  let v := pullbackZigzagRight e (equivalencePathEndpoint B 0) (equivalencePathEndpoint B 1) p
  have hv : TrivialKanFibration v := trivialKanFibration_pullbackZigzagRight _ _ _ _
  have : Quasicategory (pullback e g) := quasicategory_of_innerFibration v
  have : Quasicategory (pullbackZigzag e (equivalencePathEndpoint B 0)
      (equivalencePathEndpoint B 1) p) := quasicategory_of_innerFibration v
  have hc : equivalencePathRefl F ≫ q = p := by
    change equivalencePathRefl F ≫ (equivalencePathEndpoint F 0 ≫ p) = p
    rw [← Category.assoc, equivalencePathRefl_endpoint, Category.id_comp]
  let s : pullback e p ⟶ pullback e q :=
    pullback.lift (pullback.fst e p) (pullback.snd e p ≫ equivalencePathRefl F) (by
      rw [Category.assoc, hc, pullback.condition])
  have hst : s ≫ t = 𝟙 (pullback e p) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapRightOfComp_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullbackMapRightOfComp_snd, ← Category.assoc,
        pullback.lift_snd, Category.assoc, equivalencePathRefl_endpoint,
        Category.comp_id, Category.id_comp]
  have hs : IsQCatEquivalence s := by
    apply (isQCatEquivalence_of_trivialKanFibration t).cancel_right
    rw [hst]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have huv : u ≫ v = pullback.snd e q ≫ equivalencePathEndpoint F 1 := by
    change u ≫ (pullback.snd e g ≫ pullback.snd (equivalencePathEndpoint B 1) p) = _
    rw [← Category.assoc, pullbackMapRightOfComp_snd, Category.assoc,
      relativeEquivalencePathMapAt_snd]
  have hcomp : s ≫ (u ≫ v) = pullback.snd e p := by
    rw [huv, ← Category.assoc, pullback.lift_snd, Category.assoc,
      equivalencePathRefl_endpoint, Category.comp_id]
  rw [← hcomp]
  exact hs.comp ((isQCatEquivalence_of_trivialKanFibration u).comp
    (isQCatEquivalence_of_trivialKanFibration v))

end SerrePositivity.InfinityCategories
