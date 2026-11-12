module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroExtension
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornComponents

/-! # 零終端を持つ dg nerve の単体の外延性

概要：零終端へ向かう全成分が零なので、単体は先頭面と零終端で決まる。
方針：終端を使う成分は Hom の零性、それ以外は先頭面への単射制限で比較する。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：N7b の全境界との一致。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：端点が等しい二つの斉次 Hom の零元は異種等号で一致する。
方針：二つの端点の等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：異なる単体の零成分の比較。 -/
lemma zeroGradedHom_heq {D : Type v} [DGCategory A D] {x y x' y' : D}
    (hx : x = x') (hy : y = y') (k : ℤ) :
    HEq (0 : GradedHom A x y k) (0 : GradedHom A x' y' k) := by
  subst x'
  subst y'
  rfl

/-- 概要：零終端を持つ二単体族は先頭面が等しければ等しい。
方針：終端を使う成分は零、他の支持集合は先頭面の像として回収する。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：零終対象への境界充填の一意性。 -/
lemma Simplex.ext_of_zero_last (Z : Complex A) (hZ : IsZero Z) {n : ℕ}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1))
    (hf : s.pullback Fin.castSuccOrderEmb.toOrderHom = t.pullback Fin.castSuccOrderEmb.toOrderHom)
    (hs : s.obj (Fin.last (n + 1)) = Z) (ht : t.obj (Fin.last (n + 1)) = Z) : s = t := by
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last => exact hs.trans ht.symm
    | cast i => exact congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n => a.obj i) hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  by_cases hbLast : b = Fin.last (n + 1)
  · subst hbLast
    have hs0 : s.hom I a (Fin.last (n + 1)) k hI ha hb hk = 0 :=
      homogeneous_eq_zero_of_isZero_tgt (hs.symm ▸ hZ) _
    have ht0 : t.hom I a (Fin.last (n + 1)) k hI ha hb hk = 0 :=
      homogeneous_eq_zero_of_isZero_tgt (ht.symm ▸ hZ) _
    rw [hs0, ht0]
    exact zeroGradedHom_heq (congrFun hobj a) (congrFun hobj (Fin.last (n + 1))) k
  · have hbMax : IsGreatest (I : Set (Fin (n + 2))) b := by
      rw [hb]
      exact I.isGreatest_max' _
    have hlast : Fin.last (n + 1) ∉ I := by
      intro h
      exact hbLast (le_antisymm (Fin.le_last b) (hbMax.2 h))
    let α : Fin (n + 1) →o Fin (n + 2) := Fin.castSuccOrderEmb.toOrderHom
    let J := I.preimage α (Fin.castSucc_injective _).injOn
    have hImage : J.image α = I := by
      change (I.preimage Fin.castSucc _).image Fin.castSucc = I
      simpa only [Fin.succAbove_last] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I (Fin.last (n + 1)) hlast
    have hcard : J.card = I.card := by
      rw [← hImage, Finset.card_image_of_injOn
        (show Set.InjOn α (J : Set (Fin (n + 1))) from (Fin.castSucc_injective _).injOn)]
    have hJ : 2 ≤ J.card := by omega
    let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    have ha' : α a' = a := by
      rw [ha]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
        (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have hb' : α b' = b := by
      rw [hb]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
        (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.hom_heq_of_pullback_eq s t α α hf J a' b' k hJ rfl rfl
      (by rw [hcard]; exact hk) (Fin.castSucc_injective _).injOn (Fin.castSucc_injective _).injOn
    cases ha'
    cases hb'
    simpa only [hImage] using H

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
