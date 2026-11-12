module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HornLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OppositeSimplexYoneda
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightBoundaryCompatibility

/-!
概要：twisted arrow のホーンの面を左右の半分へ制限した値を計算する。
方針：左半分を二重反転の標準同型で元の係数に戻し、可換な射影正方形を評価する。
規約：底の quasicategory 性は不要で、単体集合の射の厳密な等式を扱う。
使われ方：ホーンの各面と左右の半分との接合。

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

/-- 始域に二重反転の逆を合成して反転した射は、再度反転すれば元の射を回収する。 -/
lemma oppositeHom_doubleInverse {A C : SSet.{u}} (g : A.op ⟶ C) :
    SSet.opFunctor.map ((SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map g) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom = g := by
  rw [SSet.opFunctor.map_comp, Category.assoc]
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality g
  change SSet.opFunctor.map (SSet.opFunctor.map g) ≫
    (SSet.opFunctorCompOpFunctorIso.app C).hom =
    (SSet.opFunctorCompOpFunctorIso.app A.op).hom ≫ g at hn
  rw [hn, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.opFunctorCompOpFunctorIso_coherence,
    ← SSet.opFunctor.map_comp, Iso.inv_hom_id, SSet.opFunctor.map_id, Category.id_comp]

/-- 二重反転の標準同型で戻した反転射を、始域側から再び反転すると元の射となる。 -/
lemma oppositeHom_doubleForward {A C : SSet.{u}} (b : A ⟶ C.op) :
    (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map b ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom) = b := by
  rw [SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.opFunctorCompOpFunctorIso_coherence]
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality b
  change SSet.opFunctor.map (SSet.opFunctor.map b) ≫
    (SSet.opFunctorCompOpFunctorIso.app C.op).hom =
    (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ b at hn
  rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 左半分を戻した図式の標準単体表示は、元の左端の単体を反転したもの。 -/
lemma oppositeSimplexInverse_normalization {C : SSet.{u}} {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ C.op) :
    (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map b ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv b)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.oppositeSimplex_yoneda ⦋n⦌
    (SSet.opFunctor.map b ≫ (SSet.opFunctorCompOpFunctorIso.app C).hom)
  rw [oppositeHom_doubleForward] at h
  apply SSet.yonedaEquiv.injective
  erw [SSet.yonedaEquiv.apply_symm_apply]
  dsimp [SSet.opObjEquiv] at h ⊢
  exact h.symm

/-- 左半分への制限は、左端射影を二重反転の標準同型で戻したもの。 -/
lemma edgewiseLeft_yoneda {C : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv f =
      SSet.opFunctor.map (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C) ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom := by
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv f
  have h : (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).inv ≫
      SSet.opFunctor.map g = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C := by
    apply SSet.yonedaEquiv.injective
    erw [SSet.yonedaEquiv_comp f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.oppositeSimplex_yoneda _ g
  rw [← h, oppositeHom_doubleInverse]

/-- 可換な射影正方形の面の右半分は、底の右成分の同じ面。 -/
lemma twistedArrowHornFace_right_restriction {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv (horn.ι i j hji ≫ a) =
      stdSimplex.δ j ≫ b ≫ snd C.op C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_yoneda, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_snd,
    ← Category.assoc a, ← Category.assoc (horn.ι i j hji), sq.w,
    ← Category.assoc, horn.ι_ι, Category.assoc]

/-- 左半分では、底の左成分の同じ面を反転して元の係数へ戻す。 -/
lemma twistedArrowHornFace_left_restriction {C : SSet.{u}} {n : ℕ}
    {i : Fin (n + 2)} (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv (horn.ι i j hji ≫ a) =
      SSet.opFunctor.map (stdSimplex.δ j) ≫ SSet.opFunctor.map (b ≫ fst C.op C) ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom := by
  rw [edgewiseLeft_yoneda]
  have h : (horn.ι i j hji ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C =
      stdSimplex.δ j ≫ b ≫ fst C.op C := by
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst,
      ← Category.assoc a, ← Category.assoc (horn.ι i j hji), sq.w,
      ← Category.assoc, horn.ι_ι, Category.assoc]
  rw [h]
  simp only [SSet.opFunctor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
