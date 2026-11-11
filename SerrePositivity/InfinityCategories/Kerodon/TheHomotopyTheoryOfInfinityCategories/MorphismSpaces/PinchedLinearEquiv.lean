module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReconstruct

/-! # 右 pinched 単体と線形方程式の解の同値

概要：全次数で実際の右 pinched 単体と線形単体の解を同定する。
方針：終端成分が同じデータは先頭面の固定条件と合わせて一致することを示し、両逆則を得る。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：加群構造と直接の線形ホーン充填。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

namespace Data

/-- 概要：右 pinched データは元の単体データで一意に決まる。
方針：端点条件は命題なので証明の一意性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：データの回収の単射性。 -/
lemma ext {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data A D x y n} (h : s.val = t.val) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- 概要：終点が最終点である任意の成分は先頭集合の回収成分と異種等号で一致する。
方針：元の集合を先頭集合と最終点で復元し、端点と次数を比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：終端成分からデータの一意性を導く。 -/
lemma hom_heq_linear_of_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data A D x y n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbLast : b = Fin.last (n + 1)) :
    HEq (s.val.hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData s).component (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hI
        (hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _))) (by
          have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast I (hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _))
          omega)) := by
  have hLast : Fin.last (n + 1) ∈ I := hbLast ▸ (show b ∈ I by rw [hb]; exact I.max'_mem _)
  have hJ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hI hLast
  have hdeg : k = 1 - ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I).card : ℤ) := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast I hLast
    omega
  refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData_component_heq s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I) k hJ hdeg).symm
  apply s.val.hom_heq_of_indices_degree
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast I hLast).symm
  · exact ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withoutLast I hI hLast).symm
  · exact hbLast
  · rfl

/-- 概要：右 pinched データの全終端成分の回収は単射。
方針：最終点を含む成分は回収族から、含まない成分は共通の定値先頭面から比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：実際の単体の再構成の逆則。 -/
lemma toLinearData_injective {n : ℕ} : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData (A := A) (D := D)
    (x := x) (y := y) (n := n)) := by
  intro s t h
  apply ext
  have ho : s.val.obj = t.val.obj := by
    funext i
    induction i using Fin.lastCases with
    | last => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.target_obj s).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.target_obj t).symm
    | cast i => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.source_obj s i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.source_obj t i).symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbLast : b = Fin.last (n + 1)
  · have hs := hom_heq_linear_of_last s I a b k hI ha hb hk hbLast
    have ht := hom_heq_linear_of_last t I a b k hI ha hb hk hbLast
    refine hs.trans (HEq.trans ?_ ht.symm)
    apply heq_of_eq
    rw [h]
  · have hLast : Fin.last (n + 1) ∉ I := by
      intro hm
      have hle : Fin.last (n + 1) ≤ b := by
        rw [hb]
        exact (I.isGreatest_max' _).2 hm
      exact hbLast (le_antisymm (Fin.le_last _) hle)
    let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I
    have hImage : J.image Fin.castSucc = I := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withoutLast, Finset.erase_eq_of_notMem hLast]
    have hcard : J.card = I.card := by
      have hc : (J.image Fin.castSucc).card = J.card :=
        Finset.card_image_of_injective _ (Fin.castSucc_injective _)
      rw [hImage] at hc
      exact hc.symm
    have hJ : 2 ≤ J.card := by omega
    have hkJ : k = 2 - (J.card : ℤ) := by omega
    have hm : IsLeast (I : Set (Fin (n + 2))) (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc := by
      rw [← hImage]
      refine ⟨Finset.mem_image.mpr ⟨_, J.min'_mem _, rfl⟩, ?_⟩
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Fin.castSucc_le_castSucc_iff.mpr ((J.isLeast_min' _).2 hj)
    have hM : IsGreatest (I : Set (Fin (n + 2))) (J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc := by
      rw [← hImage]
      refine ⟨Finset.mem_image.mpr ⟨_, J.max'_mem _, rfl⟩, ?_⟩
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Fin.castSucc_le_castSucc_iff.mpr ((J.isGreatest_max' _).2 hj)
    have haMap : a = (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc :=
      ha.trans (hm.unique (I.isLeast_min' _)).symm
    have hbMap : b = (J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc :=
      hb.trans (hM.unique (I.isGreatest_max' _)).symm
    refine HEq.trans ?_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.Data.front_hom_heq s J _ _ k hJ rfl rfl hkJ).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.Data.front_hom_heq t J _ _ k hJ rfl rfl hkJ).symm.trans ?_))
    · exact s.val.hom_heq_of_indices_degree hImage.symm haMap hbMap rfl
    · exact (t.val.hom_heq_of_indices_degree hImage.symm haMap hbMap rfl).symm

end Data

/-- 概要：実際の右 pinched 単体を回収族から再構成すると元に戻る。
方針：回収の片側の逆則と、終端成分の回収の単射性を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：全次数の同値のもう片側の逆。 -/
lemma toPinched_toLinearSimplex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s).toPinched = s := by
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.ofSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s).toPinched) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.ofSimplex s := by
    apply Data.toLinearData_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData_ofSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData_ofSimplex]
    exact congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.val hd

/-- 概要：全次数で右 pinched 単体と線形削除方程式の解は同値。
方針：終端成分の回収と、先頭面を単位・零で埋める再構成の両逆則を組み合わせる。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：実際の写像空間の加群構造と Kan 性。 -/
def linearEquiv (x y : D) (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toPinched
  left_inv := toPinched_toLinearSimplex
  right_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
