module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingIdentity

/-!
概要：輸送三角形と制限正方形の指定値から、局所比較の三角等式を回収する。
方針：指定された可逆二辺を逆向きに貼り、元の二つの等式で消去する。
規約：元の同型の値と貼り合わせ順序を保持する。
使われ方：元の全 Hom 上の大域輸送の整合性を局所自然性の整合性へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 元の三角形と正方形の等式は、指定された局所自然性の三角等式を与える。 -/
lemma functorIso_localTriangle_of_transport_and_restriction
    {X Y : SSet.{u}} {a b c d e f : X ⟶ Y}
    (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (N : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a c) (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c d)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e d) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d f)
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e f) (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b f)
    (hT : E ≪≫ D = (N ≪≫ L) ≪≫ F) (hR : R ≪≫ F = K) :
    (E.symm ≪≫ N) ≪≫ (L ≪≫ R.symm) ≪≫ K = D := by
  calc
    _ = E.symm ≪≫ (N ≪≫ L ≪≫ F) := by
      rw [← hR]
      simp only [Iso.trans_assoc, ← Iso.trans_assoc R.symm R F,
        Iso.symm_self_id, Iso.refl_trans]
    _ = E.symm ≪≫ (E ≪≫ D) := by
      rw [← Iso.trans_assoc N L F, ← hT]
    _ = D := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
