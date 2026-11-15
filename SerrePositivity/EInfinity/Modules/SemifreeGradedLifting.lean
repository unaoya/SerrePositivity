module

public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGFreeSphereHomSurjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleCoproductHomSurjective

/-!
# 半自由加群の次数付き持ち上げの法則

概要：N01 の半自由 cofibrancy のため、元の全次数 Hom の持ち上げを照合する。
方針：既存の自由 sphere・余積・全作用付き分裂の法則を使う。
規約：元の dg 加群を保ち、モデル構造を仮定しない。
使われ方：Keller, On differential graded categories, Theorem 3.2 (1) の cofibrant 対象。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：全次数 Hom の前後合成の交換の同じ成分。
方針：既存の enriched whisker exchange を評価する。
規約：符号なしの閉零射。使われ方：Keller Theorem 3.2 (1) の持ち上げの成分。 -/
lemma moduleHom_post_pre_component {M N T U : ModuleCategory A D}
    (i : M ⟶ N) (p : T ⟶ U) (q : ℤ)
    (z : (N ⟶[Complex A] T).X q) :
    (eHomWhiskerRight (Complex A) i U).f q
      ((eHomWhiskerLeft (Complex A) N p).f q z) =
    (eHomWhiskerLeft (Complex A) M p).f q
      ((eHomWhiskerRight (Complex A) i T).f q z) :=
  congrArg (fun f => f.f q z) (eHom_whisker_exchange (Complex A) i p)

/-- 概要：全作用付き分裂の一段で指定次数の持ち上げを延長する。
方針：前段の延長との差を商の Hom に戻し、同じ自由商で持ち上げる。
規約：前段と後合成の両方を保持。使われ方：Keller Theorem 3.2 (1) の cofibrancy。 -/
lemma moduleGradedSplit_postcompose_lift {M N Q T U : ModuleCategory A D}
    {i : M ⟶ N} {g : N ⟶ Q} (s : ModuleGradedSplit A D i g)
    (p : T ⟶ U) (q : ℤ)
    (hQ : Function.Surjective ((eHomWhiskerLeft (Complex A) Q p).f q))
    (a : (M ⟶[Complex A] T).X q)
    (z : (N ⟶[Complex A] U).X q)
    (h : (eHomWhiskerLeft (Complex A) M p).f q a =
      (eHomWhiskerRight (Complex A) i U).f q z) :
    ∃ b : (N ⟶[Complex A] T).X q,
      (eHomWhiskerLeft (Complex A) N p).f q b = z ∧
      (eHomWhiskerRight (Complex A) i T).f q b = a := by
  let b₀ : (N ⟶[Complex A] T).X q := s.homRestrictionSection T q a
  let w : (N ⟶[Complex A] U).X q := z - (eHomWhiskerLeft (Complex A) N p).f q b₀
  have hw : (eHomWhiskerRight (Complex A) i U).f q w = 0 := by
    dsimp only [w, b₀]
    rw [map_sub, moduleHom_post_pre_component A D, s.homRestriction_section, ← h, sub_self]
  obtain ⟨c, hc⟩ := hQ (s.homKernelRetraction U q w)
  refine ⟨b₀ + (eHomWhiskerRight (Complex A) g T).f q c, ?_, ?_⟩
  · rw [map_add, ← moduleHom_post_pre_component A D, hc,
      s.homKernel_of_restriction_zero U q w hw]
    exact add_sub_cancel _ _
  · rw [map_add, s.homKernel_restriction_zero, add_zero]
    exact s.homRestriction_section T q a

end SerrePositivity.EInfinity.Modules
