module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberInitialHorn

/-!
概要：固定始域の comma の標的射影は left fibration。
方針：一次元の辺の持ち上げ、内ホーン、高次の先頭ホーンの充填をまとめる。
規約：値域 X の quasicategory 性だけを仮定し、Y と G は任意。
使われ方：局所 Kan 添字と区間模型の fiber ごとの同値判定。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma は標的添字上の left fibration をなす。
方針：先頭ホーンを次元で分け、他の左ホーンは内ホーンとして充填する。
規約：G の fibration 性は不要。
使われ方：既存の安全な left fibration の fiber 比較定理への入力。 -/
instance unitCommaFiberProjection_leftFibration {X Y : SSet.{u}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n j hj =>
      cases n with
      | zero =>
        have hj' : j = 0 := by fin_cases j <;> simp_all
        subst j
        constructor
        intro a b sq
        let v := SSet.yonedaEquiv (horn.ι (n := 0) 0 1 (by decide) ≫ a)
        have hb : stdSimplex.δ 1 ≫ b = SSet.yonedaEquiv.symm
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x).app (Opposite.op ⦋0⦌) v) := by
          rw [← SSet.yonedaEquiv_symm_comp]
          dsimp only [v]
          rw [Equiv.symm_apply_apply, Category.assoc, sq.w, horn.ι_ι_assoc]
        obtain ⟨l, hl, hlp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_kanUnitCommaFiber_edge_lift G x v b hb
        refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := hlp }
        apply horn.hom_ext'
        intro k hk
        fin_cases k
        · exact (hk rfl).elim
        · rw [horn.ι_ι_assoc]
          change stdSimplex.δ 1 ≫ l = _
          exact hl.trans (SSet.yonedaEquiv.symm_apply_apply _)
      | succ n =>
        by_cases hzero : j = 0
        · subst j
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection_hasLiftingProperty_initialHorn G x n
        · exact InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) _
            (innerHornInclusions.intro j
              (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hzero)) hj)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
