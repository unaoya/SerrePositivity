module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HornCover
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InnerProductProjection
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の twisted arrow 射影は left fibration。
方針：各ホーンと左右の半分を固定領域へ接合し、inner anodyne な包含で延長する。
規約：元の両端射影について全ての左ホーンの持ち上げを構成し、追加の instance を仮定しない。
使われ方：実際の分類写像で空間値 Hom 関手を構成し、Yoneda 関手へ進む。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- quasicategory 上の twisted arrow の左ホーンには、左右と各面を固定した重みの延長がある。 -/
lemma exists_twistedArrowHorn_weight_extension {C : SSet.{u}} [Quasicategory C] {n : ℕ}
    {i : Fin (n + 2)} (hi : i < Fin.last (n + 1))
    (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ C,
      (∀ (j : Fin (n + 2)) (hji : j ≠ i),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j) ≫ F =
          SSet.yonedaEquiv (horn.ι i j hji ≫ a)) ∧
      ((stdSimplex.opIso ⦋n + 1⦌).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ F =
        SSet.yonedaEquiv.symm
          (SSet.opObjEquiv (SSet.yonedaEquiv (b ≫ fst C.op C)))) ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ F = b ≫ snd C.op C) := by
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_twistedArrowHornCover_gluing a b sq
  let D : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj ⦋n + 1⦌).Subcomplex :=
    ⨆ u, Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCoverMap n i u)
  have hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowWeightDomain (n + 1) i = D := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCover_range_eq i).symm
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_twistedArrowWeightDomain_extension i hi
    (Subcomplex.homOfLE hD.le ≫ G)
  have hDF : D.ι ≫ F = G := by
    have h := congrArg (fun f ↦ Subcomplex.homOfLE hD.ge ≫ f) hF
    change D.ι ≫ F = Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le ≫ G at h
    have he : Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le = 𝟙 (D : SSet.{u}) := rfl
    rw [← Category.assoc, he, Category.id_comp] at h
    exact h
  have hcover : ∀ u, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCoverMap n i u ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCoverDiagram a b u := by
    intro u
    calc
      _ = (Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCoverMap n i u)
        (le_iSup (fun v ↦ Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornCoverMap n i v)) u) ≫ D.ι) ≫ F := by
          rw [Subcomplex.lift_ι]
      _ = _ := by rw [Category.assoc, hDF, hG u]
  refine ⟨F, fun j hj ↦ hcover (some (some ⟨j, hj⟩)), ?_, hcover (some none)⟩
  exact (congrArg (fun f ↦ (stdSimplex.opIso ⦋n + 1⦌).inv ≫ f) (hcover none)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.oppositeSimplexInverse_normalization (b ≫ fst C.op C))

/-- 元の twisted arrow の両端射影は、全ての左ホーンを持ち上げる。 -/
@[kerodon 03JQ, kerodon 048H]
instance twistedArrowProjection_leftFibration (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) where
  mem := by
    intro A B f hf
    cases hf with
    | intro i hi =>
      constructor
      intro a b sq
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_horn_hasLift_iff a b sq).mpr
        (exists_twistedArrowHorn_weight_extension hi a b sq)

/-- quasicategory の twisted arrow 単体集合も quasicategory。 -/
@[kerodon 03JR]
instance twistedArrow_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) := by
  have : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)
  exact quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
