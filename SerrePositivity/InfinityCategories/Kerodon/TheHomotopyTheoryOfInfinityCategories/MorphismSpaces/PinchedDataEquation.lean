module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedDataRhs

/-! # 線形方程式から右 pinched データの単体方程式へ

概要：回収族が線形方程式を満たせば元のデータが全単体方程式を満たすと示す。
方針：最終点を含む集合は線形化、含まない集合は定値先頭面の方程式を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形解からの単体の逆構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：同じ集合と端点の成分の方程式は添字の等式に沿って一致する。
方針：集合と端点の等式を消し、証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：標準的な終端集合の方程式を元の添字へ戻す。 -/
lemma SimplexData.equation_of_indices {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {I J : Finset (Fin (n + 1))} {a b c d : Fin (n + 1)} {k : ℤ}
    {hI : 2 ≤ I.card} {ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)}
    {hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} {hk : k = 2 - (I.card : ℤ)}
    {hJ : 2 ≤ J.card} {hc : c = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)}
    {hd : d = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)} {hkJ : k = 2 - (J.card : ℤ)}
    (hIJ : I = J) (hac : a = c) (hbd : b = d)
    (he : differential A (s.hom J c d k hJ hc hd hkJ) = s.rhs J c d k hJ hc hd hkJ) :
    differential A (s.hom I a b k hI ha hb hk) = s.rhs I a b k hI ha hb hk := by
  subst J
  subst c
  subst d
  exact he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData (equation_of_indices)


namespace PinchedHom.Data

variable {x y : D}

/-- 概要：先頭埋め込みの像の集合では、右 pinched データの成分は単体方程式を満たす。
方針：先頭面が定値単体のデータであることと、単射な引き戻しの成分・右辺の計算を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：逆構成の先頭面の全方程式。 -/
lemma source_equation_on_image {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data A D x y n)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    let α := Fin.castSuccOrderEmb.toOrderHom
    differential A (s.val.hom (J.image α) (α a) (α b) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn (show Set.InjOn α (J : Set (Fin (n + 1))) from
        (Fin.castSucc_injective _).injOn)]; exact hk)) =
    s.val.rhs (J.image α) (α a) (α b) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn (show Set.InjOn α (J : Set (Fin (n + 1))) from
        (Fin.castSucc_injective _).injOn)]; exact hk) := by
  have he : differential A
      ((s.val.pullback Fin.castSuccOrderEmb.toOrderHom).hom J a b k hJ ha hb hk) =
      (s.val.pullback Fin.castSuccOrderEmb.toOrderHom).rhs J a b k hJ ha hb hk := by
    rw [s.source]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).equation
      J a b k hJ ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn] at he
  exact he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.Data (source_equation_on_image)


/-- 概要：回収族が線形方程式を満たす右 pinched データは、全ての単体方程式を満たす。
方針：最終点を含む集合は先頭集合に戻し、含まない集合は先頭面の像として扱う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形解からの単体の逆構成。 -/
lemma equation_of_linear {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data A D x y n)
    (hlinear : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data.toLinearData s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule A x y n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.val.hom I a b k hI ha hb hk) = s.val.rhs I a b k hI ha hb hk := by
  by_cases hLast : Fin.last (n + 1) ∈ I
  · let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I
    have hJ : J.Nonempty := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hI hLast
    have hdeg : k = 1 - (J.card : ℤ) := by
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast I hLast
      dsimp only [J]
      omega
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cone_equation_of_linear s J k hJ hdeg (hlinear J k hJ hdeg)
    have hbLast : b = Fin.last (n + 1) := by
      have hm : IsGreatest (I : Set (Fin (n + 2))) b := by
        rw [hb]
        exact I.isGreatest_max' _
      exact hm.unique ⟨hLast, fun _ _ => Fin.le_last _⟩
    apply s.val.equation_of_indices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast I hLast).symm ?_ hbLast he
    exact ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withoutLast I hI hLast).symm
  · let J := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast I
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
    have he := source_equation_on_image s J (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
      (J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) k hJ rfl rfl hkJ
    exact s.val.equation_of_indices hImage.symm haMap hbMap he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Data export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.Data (equation_of_linear)


end PinchedHom.Data

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
