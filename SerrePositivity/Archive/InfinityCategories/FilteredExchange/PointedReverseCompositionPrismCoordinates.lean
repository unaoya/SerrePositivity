module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ReverseCompositionPrismCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedReverseFiberCoordinates

/-!
概要：F1 の同じ全 pointed 反転合成 prism を、元の Space の全拡張単体で読む。
方針：反転錐の実座標と同じ底の反転同型を全単体の Yoneda 座標へ適用する。
規約：元の全係数を保持。使われ方：固定射の実 pointed prism との一致の証明。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 底の元の反転同型は、元の反対 Kan coherent 単体を同じ逆反転で読む。 -/
lemma reverseKanNerveSpaceIso_simplex {n : ℕ}
    (s : (SimplicialNerve KanObject.{u}ᵒᵖ) _⦋n⦌) :
    reverseKanNerveSpaceIso.hom.app (Opposite.op ⦋n⦌) (SSet.opObjEquiv.symm s) =
      coherentOppositeInverseSimplex s := rfl

/-- 同じ全 pointed 反転合成 prism の実座標は、元の反転合成単体そのもの。 -/
lemma pointedReverseKanCompositionPrism_coordinates (K L : KanObject.{u}) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (a : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K)).op _⦋n⦌)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)).op _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      (((pointedReverseKanCompositionTransportFamily K L).prism).app
        (Opposite.op ⦋n⦌) (t, a, b)).val) =
    coherentOppositeInverseSimplex
      (coherentCompositionSimplex (X := Opposite.op L) (Y := Opposite.op K)
        (Z := Opposite.op pointKanObject) (SSet.opObjEquiv b).down (SSet.opObjEquiv a).down
        (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom)) := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    (reverseKanPointCosliceIso.hom.app (Opposite.op ⦋n⦌)
      ((coherentCompositionReversePrism (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject)).app (Opposite.op ⦋n⦌) (t, a, b))).val) = _
  rw [reverseKanPointCosliceIso_app_val, coherentCompositionReversePrism_app_val]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (stdSimplex.opIso ⦋n + 1⦌).inv]
  rw [SSet.yonedaEquiv_comp, stableReverseSimplex_yoneda, Equiv.apply_symm_apply,
    reverseKanNerveSpaceIso_simplex]
  rfl

end SerrePositivity.InfinityCategories.F2
