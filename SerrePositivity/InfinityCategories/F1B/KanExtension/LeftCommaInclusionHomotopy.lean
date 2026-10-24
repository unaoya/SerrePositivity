module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaIdentityComparison

/-!
概要：oriented comma の普遍矢印を恒等矢印の包含へ制限する計算。
方針：反転前の恒等矢印の族の定値性を反転し、二重反転の同型を戻す。
規約：raw なホモトピーの射の等式を保持する。
使われ方：comma 上の Hom と元の添字上の Hom の対応の往復。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：comma の普遍矢印を恒等矢印の包含へ制限すると δ に定値となる。
方針：普遍矢印の恒等族への制限を反転前に計算し、円柱の反転の自然性を使う。
規約：K と C の quasicategory 性は不要。
使われ方：元の指定変換を comma に延長して戻す往復の計算。 -/
lemma kanLeftCommaHomotopy_inclusion_h {K C : SSet.{u}} (δ : K ⟶ C) :
    (kanLeftCommaInclusion δ ▷ (Δ[1] : SSet.{u})) ≫ (kanLeftCommaHomotopy δ).h =
      fst K (Δ[1] : SSet.{u}) ≫ δ := by
  let U := unitCommaHomotopy (𝟙 (unitComma (SSet.opFunctor.map δ)))
  let i := unitCommaIdentityFamily (SSet.opFunctor.map δ)
  have hu : (functorHomotopyPrecomp U i).h =
      fst K.op (Δ[1] : SSet.{u}) ≫ SSet.opFunctor.map δ := by
    change (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = _
    rw [← unitCommaHomotopy_precomp, Category.comp_id]
    unfold i unitCommaIdentityFamily
    rw [unitCommaHomotopy_lift_h]
  have hv : (SerrePositivity.InfinityCategories.homotopyOpposite (functorHomotopyPrecomp U i)).h =
      fst K.op.op (Δ[1] : SSet.{u}) ≫ SSet.opFunctor.map (SSet.opFunctor.map δ) := by
    dsimp only [SerrePositivity.InfinityCategories.homotopyOpposite]
    rw [hu]
    rfl
  change (((SSet.opFunctorCompOpFunctorIso.app K).inv ≫ SSet.opFunctor.map i) ▷
    (Δ[1] : SSet.{u})) ≫ (SerrePositivity.InfinityCategories.homotopyOpposite U).h ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom = _
  rw [comp_whiskerRight, Category.assoc]
  erw [← reassoc_of% (kanHomotopyOpposite_precomp_h U i), hv]
  simp only [Category.assoc]
  rw [reassoc_of% (whiskerRight_fst (SSet.opFunctorCompOpFunctorIso.app K).inv Δ[1])]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map δ) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom =
        (SSet.opFunctorCompOpFunctorIso.app K).hom ≫ δ :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality δ
  rw [hn, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F1B
