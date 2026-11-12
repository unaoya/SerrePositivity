module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：twisted arrow の射影のホーン充填を、join の重み上の延長問題へ戻す。
方針：ホーンの各面を Yoneda で取り出し、両半分で指定した底の単体を回収する。
規約：延長の存在を仮定した判定であり、quasicategory からの充填存在は後続で示す。
使われ方：空間値 Hom 関手の構成に必要な left fibration 性の組み合わせ論。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 重みの各面を延長する単体は、元の twisted arrow のホーン全体を延長する。 -/
lemma edgewiseSubdivision_horn_extension {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ C)
    (hF : ∀ (j : Fin (n + 2)) (hji : j ≠ i),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j) ≫ F =
        SSet.yonedaEquiv (horn.ι i j hji ≫ a)) :
    Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm F = a := by
  apply horn.hom_ext'
  intro j hji
  apply SSet.yonedaEquiv.injective
  rw [← Category.assoc, horn.ι_ι]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction, SSet.yonedaEquiv.apply_symm_apply]
  exact hF j hji

/-- 射影のホーン充填は、各面と左右の半分を固定した重みの延長と同値。 -/
lemma twistedArrowProjection_horn_hasLift_iff {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b) :
    sq.HasLift ↔ ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ C,
      (∀ (j : Fin (n + 2)) (hji : j ≠ i),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j) ≫ F =
          SSet.yonedaEquiv (horn.ι i j hji ≫ a)) ∧
      ((stdSimplex.opIso ⦋n + 1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ F =
        SSet.yonedaEquiv.symm
          (SSet.opObjEquiv (SSet.yonedaEquiv (b ≫ fst C.op C)))) ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ F = b ≫ snd C.op C) := by
  constructor
  · intro h
    let _ := h
    refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_, ?_⟩
    · intro j hji
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_yoneda_restriction]
      congr 1
      change stdSimplex.δ j ≫ sq.lift = _
      rw [← horn.ι_ι i j hji, Category.assoc, sq.fac_left]
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv.apply_symm_apply]
      have h := congrArg (fun f ↦ SSet.yonedaEquiv (f ≫ fst C.op C)) sq.fac_right
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst] at h
      exact congrArg SSet.opObjEquiv h
    · apply SSet.yonedaEquiv.injective
      have h := congrArg (fun f ↦ SSet.yonedaEquiv (f ≫ snd C.op C)) sq.fac_right
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd] at h
      exact h
  · rintro ⟨F, hF, hL, hR⟩
    refine CommSq.HasLift.mk'
      { l := SSet.yonedaEquiv.symm F
        fac_left := edgewiseSubdivision_horn_extension a F hF
        fac_right := ?_ }
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst]
      apply SSet.yonedaEquiv.injective
      erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
      apply SSet.opObjEquiv.injective
      change SSet.yonedaEquiv ((stdSimplex.opIso ⦋n + 1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ F) = _
      rw [hL, SSet.yonedaEquiv.apply_symm_apply]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd]
      apply SSet.yonedaEquiv.injective
      erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ F) = _
      rw [hR]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
