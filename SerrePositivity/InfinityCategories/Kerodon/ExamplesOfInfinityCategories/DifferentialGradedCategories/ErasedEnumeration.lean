module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeCoordinateFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathEvaluation

/-!
# 一座標を削除した有限集合の番号付け

概要：有限集合の番号付けから指定座標を除いた番号付けを作る。
方針：succAbove によって指定番号を飛ばし、有限集合の erase の部分型へ移す。
規約：残る座標の相対順序を変えない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の削除面の向きの同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：一座標を除いた番号付けは残る有限集合への同値となる。
方針：succAbove の単射性と指定点以外への全射性を使う。
規約：元の番号付けは任意でよく、昇順性を仮定しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体の座標0面の番号付け。 -/
def erasedEnumeration {A : Type u} [DecidableEq A] {S : Finset A} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) : Fin m ≃ ↥(S.erase (e i).val) :=
  Equiv.ofBijective (fun j ↦ ⟨(e (i.succAbove j)).val,
    Finset.mem_erase.mpr ⟨fun h ↦ Fin.succAbove_ne i j (e.injective (Subtype.ext h)),
      (e (i.succAbove j)).property⟩⟩) (by
    constructor
    · intro j k h
      apply i.succAboveOrderEmb.injective
      apply e.injective
      apply Subtype.ext
      exact congrArg (fun z : ↥(S.erase (e i).val) ↦ z.val) h
    · intro a
      let b : S := ⟨a.val, Finset.mem_of_mem_erase a.property⟩
      have hb : e.symm b ≠ i := by
        intro h
        have he : b = e i := by simpa using congrArg e h
        exact (Finset.mem_erase.mp a.property).1 (congrArg Subtype.val he)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
      refine ⟨j, Subtype.ext ?_⟩
      change (e (i.succAbove j)).val = a.val
      rw [hj, e.apply_symm_apply])

/-- 概要：削除した番号付けの値は元の番号付けで指定点を飛ばした値である。
方針：同値の順方向の定義を評価する。
規約：部分型の証明を除いた元の集合の値の等式。
使われ方：HA 1.3.1.16 の削除面の像の計算。 -/
lemma erasedEnumeration_val {A : Type u} [DecidableEq A] {S : Finset A} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) (j : Fin m) :
    (erasedEnumeration e i j).val = (e (i.succAbove j)).val := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
