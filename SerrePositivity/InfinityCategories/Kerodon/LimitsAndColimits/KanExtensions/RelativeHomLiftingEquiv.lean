module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinInvertingRestriction

/-!
概要：関手の族の制限の持ち上げと、二つの部分図式を保つ実際の図式の延長を同定する。
方針：相対指数の普遍性と前合成の自然性を両方向に適用する。
規約：充填性や quasicategory 性は不要。
使われ方：族の相対骨格上の延長を相対 join 上の図式へ戻す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：二つの部分図式を固定した延長は、族の制限の持ち上げと同値。
方針：curry の自然性で順方向を示し、底への射影を復元して逆方向を uncurry する。
規約：底上の射 i とパラメータの射 j は任意。
使われ方：相対 join の族の延長を実際の図式の延長へ移す。 -/
lemma kanRelativeHomDiagram_lift_iff {C D A A₀ : SSet.{u}}
    {K L : Over C} (i : K ⟶ L) (j : A₀ ⟶ A) (c : A ⟶ C)
    (F : pullback c K.hom ⟶ D) (G : pullback (j ≫ c) L.hom ⟶ D) :
    (∃ H : pullback c L.hom ⟶ D,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i (Over.mk c) ≫ H = F ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom).map
          (Over.homMk j rfl : Over.mk (j ≫ c) ⟶ Over.mk c) ≫ H = G) ↔
    ∃ l : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom L.hom D,
      j ≫ l = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom (j ≫ c) G ∧
        l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry K.hom c F := by
  constructor
  · rintro ⟨H, hHK, hHL⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom c H, ?_, ?_⟩
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp]
      rw [hHL]
    · erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre i, hHK]
  · rintro ⟨l, hlj, hli⟩
    have hlp : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D = c := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_projection (D := D) i, ← Category.assoc,
        hli, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection]
    let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) L.hom c).symm ⟨l, hlp⟩
    have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom c H = l :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) L.hom c).apply_symm_apply ⟨l, hlp⟩)
    refine ⟨H, ?_, ?_⟩
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_injective K.hom c
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre i, hH]
      exact hli
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_injective L.hom (j ≫ c)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp, hH]
      exact hlj

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
