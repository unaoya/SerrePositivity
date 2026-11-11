module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoprodTensorGlue
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily

/-!
概要：余積形状の相対関手空間を、二枝の相対関手空間の直積と同定する。
方針：全パラメータ族を厳密に貼り合わせ、二つの制限で逆を検証する。
規約：射影や形状の充填性は不要。使われ方：固定初期値の終点評価を引き戻しで表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {D C E B : SSet.{u}} (p : E ⟶ B) (β : D ⨿ C ⟶ B)

/-- 相対関手の両枝の全族を、元の余積の底を保つ同じ族に貼る。 -/
def relativeFunctorCoprodCurry {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inl ≫ β))
    (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inr ≫ β)) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry b))
    (by
      apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensor_hom_ext
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
          whiskerRight_fst_assoc]
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
          whiskerRight_fst_assoc])

/-- 貼った相対族の左制限は、同じ元の左族。 -/
lemma relativeFunctorCoprodCurry_inl {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inl ≫ β))
    (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inr ≫ β)) :
    relativeFunctorCoprodCurry p β a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inl = a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (coprod.inl ≫ β)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, relativeFunctorCoprodCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inl]

/-- 貼った相対族の右制限も、同じ元の右族。 -/
lemma relativeFunctorCoprodCurry_inr {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inl ≫ β))
    (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inr ≫ β)) :
    relativeFunctorCoprodCurry p β a b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inr = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (coprod.inr ≫ β)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, relativeFunctorCoprodCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inr]

/-- 二つの制限が一致する相対族は、同じ余積上で厳密に一致する。 -/
lemma relativeFunctorCoprod_hom_ext {T : SSet.{u}} {a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β}
    (h₀ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inl = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inl)
    (h₁ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inr = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inr) :
    a = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p β
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensor_hom_ext
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre a coprod.inl).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry h₀).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre b coprod.inl))
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre a coprod.inr).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry h₁).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre b coprod.inr))

/-- 余積上の相対関手を両枝へ同時に制限する射。 -/
def relativeFunctorCoprodPair :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inl ≫ β) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inr ≫ β) :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inl) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β coprod.inr)

/-- 両枝への同時制限は、相対関手空間の厳密な同型。 -/
def relativeFunctorCoprodPairIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inl ≫ β) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (coprod.inr ≫ β) where
  hom := relativeFunctorCoprodPair p β
  inv := relativeFunctorCoprodCurry p β (fst _ _) (snd _ _)
  hom_inv_id := by
    apply relativeFunctorCoprod_hom_ext p β
    · rw [Category.assoc, relativeFunctorCoprodCurry_inl, relativeFunctorCoprodPair, lift_fst,
        Category.id_comp]
    · rw [Category.assoc, relativeFunctorCoprodCurry_inr, relativeFunctorCoprodPair, lift_snd,
        Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, relativeFunctorCoprodPair, lift_fst,
        relativeFunctorCoprodCurry_inl, Category.id_comp]
    · rw [Category.assoc, relativeFunctorCoprodPair, lift_snd,
        relativeFunctorCoprodCurry_inr, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
