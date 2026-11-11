module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeTransportPrism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 余錐の制限射の辺の持ち上げ

概要：関手圏の図式の辺を、終点の余錐を固定して余錐の辺へ持ち上げられる。
方針：図式の辺を prism に直し、頂点を固定した余錐の輸送を使う。
規約：この存在定理は cartesian 性まで主張しない。使われ方：余錐の相対充填の輸送。

対応節は Kerodon 5.3（Tag 035A）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：余錐の制限射は、終点を固定した図式の辺を持ち上げる。
方針：辺を実際の prism として輸送し、再び関手の辺へ curry する。
規約：値域は quasicategory、形状は任意。cartesian 性の証明は別である。
使われ方：余錐の制限射の輸送の存在部分。 -/
lemma coconeRestriction_hasLiftingProperty_finalVertex (K X : SSet.{u}) [Quasicategory X] :
    HasLiftingProperty (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) := by
  constructor
  intro g b sq
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).symm (SSet.yonedaEquiv g)
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = SSet.yonedaEquiv g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).apply_symm_apply _
  let H := (β_ (Δ[1] : SSet.{u}) K).hom ≫ uncurry b
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have he := congrArg SSet.yonedaEquiv sq.w
    rw [SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp, ← hF] at he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F) =
      ((ihom K).obj X).δ 0 (SSet.yonedaEquiv b) at he
    rw [he]
    have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one (SSet.yonedaEquiv b)
    rw [Equiv.symm_apply_apply] at hb
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₁ ≫ uncurry b) = _
    exact hb
  obtain ⟨L, hL₁, hLK, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cocone_fixedVertex_prism F H hH
  let l := curry ((β_ T (Δ[1] : SSet.{u})).hom ≫ L)
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    change ((ihom T).obj X).δ 0 (SSet.yonedaEquiv l) = SSet.yonedaEquiv g
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one, Equiv.symm_apply_apply]
    dsimp only [l]
    rw [uncurry_curry]
    have hs : SSet.ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T := rfl
    rw [← Category.assoc, hs, hL₁, hF]
  · apply uncurry_injective
    dsimp only [l]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction, uncurry_pre_app, uncurry_curry]
    have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ (β_ T (Δ[1] : SSet.{u})).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) := rfl
    rw [← Category.assoc, hs, Category.assoc, hLK]
    dsimp only [H]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
