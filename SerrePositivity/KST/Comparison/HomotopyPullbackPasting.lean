module

public import SerrePositivity.KST.Comparison.FibrantSquareCriterion
public import SerrePositivity.KST.Comparison.HomotopyPullbackInvariance

/-!
# 中央の縦射が Kan な四角形の横の貼り合わせ

概要：二つのホモトピー引き戻しを、中央の Kan fibration を使って横に貼り合わせる。
方針：右端の縦射の Kan 分解と、固定基底での厳密ファイバーの不変性を使う。
規約：Segal 1974 Lemmas 1.7・1.8 の各段階の四角形への補助。右端の Kan 性は不要。
使われ方：余積への各成分の包含から、円筒・telescope への包含へ進める。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：中央の縦射が Kan fibration の二つのホモトピー引き戻しは、外周もホモトピー引き戻しにする。
方針：二つの厳密ファイバーの比較を引き戻し、普遍性による同型と合成する。
規約：基底や右端の縦射には Kan 性を課さない。
使われ方：Segal Lemma 1.8 の各段階から telescope への四角形。
-/
theorem isHomotopyPullback_paste_horiz_of_middle_fibration
    {P X Z Y B C : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} {c : X ⟶ Z} {p : Z ⟶ C} {d : B ⟶ C}
    (s : CommSq a b f g) (t : CommSq c f p d)
    (hs : IsHomotopyPullback s) (ht : IsHomotopyPullback t)
    (hf : SSet.modelCategoryQuillen.J.rlp f) :
    IsHomotopyPullback (s.horiz_comp t) := by
  let dp := AnodyneKanReplacement.factorization.factorizationData p
  let k := alternativePullbackComparison t.flip dp.i dp.p dp.fac
  let q := pullback.fst d dp.p
  have hq : SSet.modelCategoryQuillen.J.rlp q :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst d dp.p dp.hp
  have hkq : k ≫ q = f := alternativePullbackComparison_fst ..
  have hks : k ≫ pullback.snd d dp.p = c ≫ dp.i := alternativePullbackComparison_snd ..
  have hk : IsIso (AnodyneHomotopy.anodyneQ.map k) :=
    (isHomotopyPullback_iff_alternative t.flip dp.i dp.hi dp.p dp.hp dp.fac).mp
      ((isHomotopyPullback_flip_iff t).mpr ht)
  let l : P ⟶ pullback g f := pullback.lift b a s.w.symm
  have hl : IsIso (AnodyneHomotopy.anodyneQ.map l) :=
    (isHomotopyPullback_iff_strict_of_left_fibration s hf).mp hs
  let m := pullbackMapBase f q g k hkq
  have hm : IsIso (AnodyneHomotopy.anodyneQ.map m) :=
    pullbackMapBase_localized_isIso f hf q hq g k hkq hk
  have hU : IsPullback
      (pullback.snd g q ≫ pullback.snd d dp.p) (pullback.fst g q) dp.p (g ≫ d) :=
    (IsPullback.of_hasPullback g q).flip.paste_horiz
      (IsPullback.of_hasPullback d dp.p).flip
  let e := hU.flip.isoPullback
  have heF : e.hom ≫ pullback.fst (g ≫ d) dp.p = pullback.fst g q :=
    hU.flip.isoPullback_hom_fst
  have heS : e.hom ≫ pullback.snd (g ≫ d) dp.p =
      pullback.snd g q ≫ pullback.snd d dp.p := hU.flip.isoPullback_hom_snd
  have hcomp : l ≫ m ≫ e.hom =
      alternativePullbackComparison (s.horiz_comp t).flip dp.i dp.p dp.fac := by
    apply pullback.hom_ext
    · simp only [Category.assoc, heF, alternativePullbackComparison_fst]
      rw [show m ≫ pullback.fst g q = pullback.fst g f from pullbackMapBase_fst ..]
      exact pullback.lift_fst b a s.w.symm
    · have hmS : m ≫ pullback.snd g q = pullback.snd g f ≫ k :=
        pullbackMapBase_snd ..
      calc
        _ = l ≫ m ≫ (e.hom ≫ pullback.snd (g ≫ d) dp.p) := by simp [Category.assoc]
        _ = l ≫ m ≫ (pullback.snd g q ≫ pullback.snd d dp.p) := by rw [heS]
        _ = l ≫ (m ≫ pullback.snd g q) ≫ pullback.snd d dp.p := by simp [Category.assoc]
        _ = l ≫ (pullback.snd g f ≫ k) ≫ pullback.snd d dp.p := by rw [hmS]
        _ = (l ≫ pullback.snd g f) ≫ (k ≫ pullback.snd d dp.p) := by simp [Category.assoc]
        _ = a ≫ (c ≫ dp.i) := by rw [hks, show l ≫ pullback.snd g f = a from pullback.lift_snd ..]
        _ = _ := by rw [alternativePullbackComparison_snd]; simp [Category.assoc]
  apply (isHomotopyPullback_flip_iff (s.horiz_comp t)).mp
  apply (isHomotopyPullback_iff_alternative (s.horiz_comp t).flip
    dp.i dp.hi dp.p dp.hp dp.fac).mpr
  rw [← hcomp, Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
