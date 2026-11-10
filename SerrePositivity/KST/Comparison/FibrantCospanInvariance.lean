module

public import SerrePositivity.KST.Comparison.FibrantPullbackMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 基底も動かす Kan fibration の引き戻し比較

概要：右の脚が Kan fibration である cospan の三成分の局所化同型は、引き戻しの局所化同型を誘導する。
方針：右の脚を新しい基底から引き戻し、固定基底での比較と左入力の比較に分ける。
規約：Segal 1974 Proposition 1.6 のホモトピー引き戻しの模型不変性への補助。
使われ方：基底を含む三つの入力を同時に置換する。
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
概要：右の脚が Kan fibration である二つの cospan の局所化可逆な比較は、引き戻しで可逆となる。
方針：基底の比較に沿って右の脚を引き戻し、固定基底の比較と左入力の引き戻しを合成する。
規約：基底の Kan 性は不要。比較射は二つの射影の等式で指定する。
使われ方：ホモトピー引き戻し模型の三入力の不変性。
-/
@[kerodon 0109]
theorem fibrantCospanMap_localized_isIso {X E B X' E' B' : SSet.{u}}
    (f : X ⟶ B) (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (f' : X' ⟶ B') (p' : E' ⟶ B') (hp' : SSet.modelCategoryQuillen.J.rlp p')
    (a : X ⟶ X') (b : E ⟶ E') (c : B ⟶ B')
    (hf : f ≫ c = a ≫ f') (hb : p ≫ c = b ≫ p')
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hbi : IsIso (AnodyneHomotopy.anodyneQ.map b))
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map c))
    (m : pullback f p ⟶ pullback f' p')
    (hmf : m ≫ pullback.fst f' p' = pullback.fst f p ≫ a)
    (hms : m ≫ pullback.snd f' p' = pullback.snd f p ≫ b) :
    IsIso (AnodyneHomotopy.anodyneQ.map m) := by
  let q := pullback.fst c p'
  let e := pullback.snd c p'
  have hq : SSet.modelCategoryQuillen.J.rlp q :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst c p' hp'
  have he : IsIso (AnodyneHomotopy.anodyneQ.map e) :=
    pullback_localized_isIso c hc p' hp' e q (IsPullback.of_hasPullback c p').flip
  let z : E ⟶ pullback c p' := pullback.lift p b hb
  have hzq : z ≫ q = p := pullback.lift_fst ..
  have hze : z ≫ e = b := pullback.lift_snd ..
  have hz : IsIso (AnodyneHomotopy.anodyneQ.map z) := by
    have hcomp : IsIso (AnodyneHomotopy.anodyneQ.map z ≫ AnodyneHomotopy.anodyneQ.map e) := by
      rw [← Functor.map_comp, hze]
      exact hbi
    exact (isIso_comp_right_iff _ _).mp hcomp
  let r := pullbackMapBase p q f z hzq
  have hr : IsIso (AnodyneHomotopy.anodyneQ.map r) :=
    pullbackMapBase_localized_isIso p hp q hq f z hzq hz
  have hqc : q ≫ c = e ≫ p' := pullback.condition
  have hscond : (pullback.fst f q ≫ a) ≫ f' = (pullback.snd f q ≫ e) ≫ p' := by
    calc
      _ = pullback.fst f q ≫ (a ≫ f') := Category.assoc _ _ _
      _ = pullback.fst f q ≫ (f ≫ c) := congrArg (fun v => pullback.fst f q ≫ v) hf.symm
      _ = (pullback.fst f q ≫ f) ≫ c := (Category.assoc _ _ _).symm
      _ = (pullback.snd f q ≫ q) ≫ c :=
        congrArg (fun v => v ≫ c) (pullback.condition (f := f) (g := q))
      _ = pullback.snd f q ≫ (e ≫ p') := by rw [Category.assoc, hqc]
      _ = _ := (Category.assoc _ _ _).symm
  let s : pullback f q ⟶ pullback f' p' :=
    pullback.lift (pullback.fst f q ≫ a) (pullback.snd f q ≫ e) hscond
  have hsf : s ≫ pullback.fst f' p' = pullback.fst f q ≫ a := pullback.lift_fst ..
  have hss : s ≫ pullback.snd f' p' = pullback.snd f q ≫ e := pullback.lift_snd ..
  have hwhole : IsPullback (pullback.snd f q ≫ e) (pullback.fst f q) p' (f ≫ c) :=
    (IsPullback.of_hasPullback f q).flip.paste_horiz (IsPullback.of_hasPullback c p').flip
  have hlong : IsPullback (s ≫ pullback.snd f' p') (pullback.fst f q) p' (a ≫ f') := by
    simpa only [hss, ← hf] using hwhole
  have hspb : IsPullback s (pullback.fst f q) (pullback.fst f' p') a :=
    hlong.of_right hsf (IsPullback.of_hasPullback f' p').flip
  have hs : IsIso (AnodyneHomotopy.anodyneQ.map s) :=
    pullback_localized_isIso a ha (pullback.fst f' p')
      (SSet.modelCategoryQuillen.J.rlp.pullback_fst f' p' hp') s (pullback.fst f q) hspb
  have hfac : m = r ≫ s := by
    apply pullback.hom_ext
    · rw [hmf, Category.assoc, hsf, ← Category.assoc, pullbackMapBase_fst]
    · rw [hms, Category.assoc, hss, ← Category.assoc, pullbackMapBase_snd,
        Category.assoc, hze]
  rw [hfac, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
