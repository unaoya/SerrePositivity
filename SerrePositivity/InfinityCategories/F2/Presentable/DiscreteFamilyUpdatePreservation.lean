module

public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteFamilyUpdate
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedConstantColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedFunctorOperations
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.FunctorPointwiseColimitCriterion

/-!
概要：離散図式の一成分更新関手は小さい sifted 余極限を保存する。
方針：更新座標では恒等、他の座標では定値関手の保存性を使う。
規約：元の全図式族と指定余錐を保つ。
使われ方：有限余積比較の可逆性を各座標の Yoneda 生成で検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：一成分更新関手は元の任意の小さい sifted 余極限を保存する。
方針：元の全余錐の像の各座標を判定して関手圏の余極限へまとめる。
規約：添字の有限性は不要。
使われ方：有限余積比較の各変数での保存。 -/
lemma discreteFamilyUpdate_preservesSmallSiftedColimits {I : Type u} {X : SSet.{u + 1}}
    [Quasicategory X]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) (i : I) :
    PreservesSmallSiftedColimits (discreteFamilyUpdate p i) := by
  intro J hJ d c hc
  apply isColimitCone_of_pointwise
  rintro ⟨j⟩
  obtain ⟨⟨j⟩, rfl⟩ := nerveEquiv.symm.surjective j
  have hpres : PreservesSmallSiftedColimits
      (discreteFamilyUpdate p i ≫ evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk j)))) := by
    rw [discreteFamilyUpdate_evaluate]
    split_ifs
    · exact identity_preservesSmallSiftedColimits X
    · exact constant_preservesSmallSiftedColimits _
  have h := hpres J d c hc
  have hv : (evaluateFunctorCocone (mapJoinCocone (discreteFamilyUpdate p i) c)
      (ULift.up (nerveVertex (Discrete.mk j)))).val =
      (mapJoinCocone (discreteFamilyUpdate p i ≫
        evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk j)))) c).val := rfl
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr h

end SerrePositivity.InfinityCategories.F2.Presentable
