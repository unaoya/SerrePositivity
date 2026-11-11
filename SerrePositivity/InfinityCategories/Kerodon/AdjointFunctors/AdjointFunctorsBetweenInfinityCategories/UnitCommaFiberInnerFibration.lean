module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberEdgeLift

/-!
概要：固定始域の comma の標的射影は inner fibration。
方針：端点の組への既存の inner fibration で充填し、始域の定値 fiber へ戻す。
規約：矢印の値域 X の quasicategory 性だけを使う。
使われ方：局所 Kan 添字の区間模型の left fibration 性の内ホーン部分。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma の標的射影は任意の内ホーンを持ち上げる。
方針：標的の単体に定値の始域を添え、端点の組への充填を fiber に制限する。
規約：G 自体や Y の充填性は要求しない。
使われ方：left fibration の構造の内ホーンの条件。 -/
instance unitCommaFiberProjection_innerFibration {X Y : SSet.{u}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) where
  mem := by
    intro A B i hi
    constructor
    intro a b sq
    let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
    let d := lift (SSet.const x : B ⟶ X) b
    have hw : (a ≫ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaPair G = i ≫ d := by
      apply CartesianMonoidalCategory.hom_ext
      · change a ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = i ≫ d ≫ fst X Y
        rw [show r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = SSet.const x from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _,
          SSet.comp_const]
        simp only [d, lift_fst, SSet.comp_const]
      · change a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x = i ≫ d ≫ snd X Y
        simpa only [d, Category.assoc, lift_snd] using sq.w
    have := InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaPair G) i hi
    let s : CommSq (a ≫ r) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaPair G) d := ⟨hw⟩
    have hsource : s.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = SSet.const x := by
      have h := s.fac_right =≫ fst X Y
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource, d, Category.assoc, lift_fst] using h
    have htarget : s.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = b := by
      have h := s.fac_right =≫ snd X Y
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget, d, Category.assoc, lift_snd] using h
    refine CommSq.HasLift.mk' {
      l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x s.lift hsource
      fac_left := ?_
      fac_right := ?_ }
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact s.fac_left
    · change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) = b
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact htarget

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
