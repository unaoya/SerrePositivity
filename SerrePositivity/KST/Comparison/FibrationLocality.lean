module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 厳密な引き戻しの覆いに沿う持ち上げ性の局所性

概要：持ち上げ問題の底の写像が一片へ因子化するなら、その片での引き戻しの持ち上げを使える。
方針：引き戻しの普遍性で上の写像も一片へ移し、充填を全空間へ合成する。
規約：Mather 1976 §4 Theorem 18、Lemmas 19–23 に向けた厳密な単体集合の補助。
原典の WCHP の論証や、ホモトピー引き戻しの貼り合わせを仮定しない。
使われ方：pushout の各片での Kan fibration の全体への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped Simplicial

/--
概要：右射の引き戻しへ底の各写像を移せるなら、その引き戻しでの持ち上げ性は全体で使える。
方針：上の写像を引き戻しへ持ち上げ、局所的な対角射を元の全空間へ合成する。
規約：左射は horn に限らない任意の射。
使われ方：単体ごとの覆いから Kan 条件を得る。
-/
theorem lifting_of_pullbackFactorizations {A D E B : SSet.{u}} (i : A ⟶ D) (p : E ⟶ B)
    (hlocal : ∀ v : D ⟶ B, ∃ (U V : SSet.{u}) (iU : U ⟶ B) (iV : V ⟶ E)
      (q : V ⟶ U) (vU : D ⟶ U), IsPullback iV q p iU ∧
        HasLiftingProperty i q ∧ vU ≫ iU = v) : HasLiftingProperty i p := by
  constructor
  intro a b sq
  obtain ⟨U, V, iU, iV, q, bU, hpb, hq, hb⟩ := hlocal b
  have hcomm : a ≫ p = (i ≫ bU) ≫ iU := by rw [Category.assoc, hb]; exact sq.w
  obtain ⟨aV, haV, haQ⟩ := hpb.exists_lift a (i ≫ bU) hcomm
  let sqV : CommSq aV i q bU := ⟨haQ⟩
  let := hq
  refine ⟨⟨{ l := sqV.lift ≫ iV, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, sqV.fac_left, haV]
  · rw [Category.assoc, hpb.w, ← Category.assoc, sqV.fac_right, hb]

/--
概要：pushout の二つの片での厳密な引き戻しが Kan fibration なら、全体も Kan fibration である。
方針：底の標準単体を、次数ごとの pushout の共同全射性で一片へ移す。
規約：上側の pushout や貼り付けの単射性は仮定しない。
使われ方：厳密な二重写像円筒の比較の Kan 条件。
-/
theorem kanFibration_of_pushoutCover {W X Y B E EX EY : SSet.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {iX : X ⟶ B} {iY : Y ⟶ B}
    (hpush : IsPushout f g iX iY) (p : E ⟶ B)
    (qX : EX ⟶ X) (jX : EX ⟶ E) (hX : IsPullback jX qX p iX)
    (qY : EY ⟶ Y) (jY : EY ⟶ E) (hY : IsPullback jY qY p iY)
    (hqX : SSet.modelCategoryQuillen.J.rlp qX) (hqY : SSet.modelCategoryQuillen.J.rlp qY) :
    SSet.modelCategoryQuillen.J.rlp p := by
  intro A D i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  apply lifting_of_pullbackFactorizations (SSet.horn (n + 1) k).ι p
  intro b
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n + 1⦌)
  obtain ⟨x, hx⟩ | ⟨y, hy⟩ :=
    Types.eq_or_eq_of_isPushout (hpush.map ev) (SSet.yonedaEquiv b)
  · refine ⟨_, _, iX, jX, qX, SSet.yonedaEquiv.symm x, hX,
      hqX _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k), ?_⟩
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hx
  · refine ⟨_, _, iY, jY, qY, SSet.yonedaEquiv.symm y, hY,
      hqY _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k), ?_⟩
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hy

end SerrePositivity.KST.Comparison
