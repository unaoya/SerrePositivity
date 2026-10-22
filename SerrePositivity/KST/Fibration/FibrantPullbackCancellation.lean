module
public import SerrePositivity.KST.Comparison.HomotopyPullbackPasting

/-! # 中央が Kan な場合のホモトピー引き戻しの右消去 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 右と外周が homotopy pullback なら左もそうなる。中央の Kan 条件を使う。 -/
theorem isHomotopyPullback_left_of_horiz_of_middle_fibration
    {P X Z Y B C : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} {c : X ⟶ Z} {p : Z ⟶ C} {d : B ⟶ C}
    (s : CommSq a b f g) (t : CommSq c f p d)
    (hout : IsHomotopyPullback (s.horiz_comp t)) (ht : IsHomotopyPullback t)
    (hf : SSet.modelCategoryQuillen.J.rlp f) :
    IsHomotopyPullback s := by
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
        _ = a ≫ (c ≫ dp.i) := by
          rw [hks, show l ≫ pullback.snd g f = a from pullback.lift_snd ..]
        _ = _ := by
          rw [alternativePullbackComparison_snd]
          simp [Category.assoc]
  have ho := (isHomotopyPullback_iff_alternative (s.horiz_comp t).flip
    dp.i dp.hi dp.p dp.hp dp.fac).mp
      ((isHomotopyPullback_flip_iff (s.horiz_comp t)).mpr hout)
  rw [← hcomp, Functor.map_comp, Functor.map_comp] at ho
  have : IsIso (AnodyneHomotopy.anodyneQ.map m ≫
      AnodyneHomotopy.anodyneQ.map e.hom) := by infer_instance
  have hl : IsIso (AnodyneHomotopy.anodyneQ.map l) :=
    (isIso_comp_right_iff _ _).mp ho
  exact (isHomotopyPullback_iff_strict_of_left_fibration s hf).mpr hl

end SerrePositivity.KST.Fibration
