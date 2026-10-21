module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelNativeCommonImages
public import SerrePositivity.InfinityCategories.F2.FunctorIsoPostcompFaithful

/-!
概要：実模型と native 切断を結ぶ二脚の指定同型は、共通の底で整合する。
方針：元の native path の合成式で逆同型を相殺し、共通点同型の後合成の忠実性で戻す。
規約：両端の等式は元の引き戻し条件から明示。使われ方：実模型比較全体の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 等式で始点だけ表示変更した指定同型は、元の指定値と型付きで一致する。 -/
lemma iso_eqToIso_trans_heq {D : Type*} [Category D] {a b c : D} (h : a = b) (e : b ≅ c) :
    HEq (eqToIso h ≪≫ e) e := by
  subst b
  exact heq_of_eq (Iso.refl_trans e)

variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "I" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local notation "L" => coherentCospanNativeLeftFinalFiberIso F X Y Z C b
local notation "R" => coherentCospanNativeRightFinalFiberIso F X Y Z C b
local notation "P" => coherentCospanNativeSectionFiberPathIso F X Y Z C b
local notation "l" => coherentCospanModelNativeLeftIso F X Y Z C b
local notation "r" => coherentCospanModelNativeRightIso F X Y Z C b

/-- 同じ元の二脚の指定比較は、元の厳密な引き戻しの底で型付きで一致する。 -/
lemma coherentCospanModelNativeLegCompatibility : HEq ((l).postcomp f) ((r).postcomp g) := by
  have hc : HEq (L ≪≫ P) R := by
    unfold coherentCospanNativeSectionFiberPathIso
    rw [← Iso.trans_assoc, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
    exact iso_eqToIso_trans_heq _ _
  have hl := (coherentCospanModelNativeLeftCommonImage_heq F X Y Z C b).trans hc
  have hr := coherentCospanModelNativeRightCommonImage_heq F X Y Z C b
  apply functorIso_postcomp_iso_reflects_heq I ((l).postcomp f) ((r).postcomp g)
  · simp only [Category.assoc, pullback.condition]
  · simp only [Category.assoc, pullback.condition]
  · exact hl.trans hr.symm

end SerrePositivity.InfinityCategories.F2
