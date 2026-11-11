module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroExtensionality

/-! # 選んだ面と未知成分による単体データの外延性

概要：全頂点を覆う面の値が一致し、残る成分が零なら二つの単体データは等しい。
方針：対象は面の値から回収し、既知成分は被覆面、未知成分は零で比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：cospan の二セルの零未知データの共通面の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：全頂点を覆う選んだ面で一致する単体データは同じ対象族を持つ。
方針：各頂点を避ける選んだ面を取り、その面の一頂点で制限の等式を評価する。
規約：HA Proposition 1.3.1.10。使われ方：既知面から全対象の一致を得る。 -/
lemma obj_eq_of_selected_faces {n : ℕ} (S : Finset (Fin (n + 2)))
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hfaces : ∀ j ∈ S, s.pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom) : s.obj = t.obj := by
  funext k
  obtain ⟨j, hjS, hjk⟩ := hS k
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hjk.symm
  have h := congrArg (fun d : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n => d.obj k') (hfaces j hjS)
  change s.obj (j.succAbove k') = t.obj (j.succAbove k') at h
  simpa only [hk'] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (obj_eq_of_selected_faces)


/-- 概要：選んだ面で一致し、未知成分がともに零のデータは等しい。
方針：対象の一致を面から得て、既知成分をその集合を含む面、未知成分を零で比較する。
規約：HA Proposition 1.3.1.10。使われ方：左右の零未知データの共通面の一意性。 -/
lemma ext_of_selected_faces_zero_unknown {n : ℕ} (S : Finset (Fin (n + 2)))
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hfaces : ∀ j ∈ S, s.pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom)
    (hs0 : ∀ I, S ⊆ I → ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0)
    (ht0 : ∀ I, S ⊆ I → ∀ a b k hI ha hb hk, t.hom I a b k hI ha hb hk = 0) : s = t := by
  have hobj := obj_eq_of_selected_faces S hS s t hfaces
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  by_cases hknown : ∃ j ∈ S, j ∉ I
  · obtain ⟨j, hjS, hj⟩ := hknown
    let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
    have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
    have hJ : 2 ≤ J.card := by omega
    have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
    let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    have ha' : j.succAboveOrderEmb.toOrderHom a' = a := by
      rw [ha]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min
        (f := j.succAboveOrderEmb.toOrderHom) j.succAboveOrderEmb.monotone
        (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have hb' : j.succAboveOrderEmb.toOrderHom b' = b := by
      rw [hb]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max
        (f := j.succAboveOrderEmb.toOrderHom) j.succAboveOrderEmb.monotone
        (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq s t j.succAboveOrderEmb.toOrderHom
      j.succAboveOrderEmb.toOrderHom (hfaces j hjS) J a' b' k hJ rfl rfl
      (by rw [hcard]; exact hk) j.succAboveOrderEmb.injective.injOn
      j.succAboveOrderEmb.injective.injOn
    cases ha'
    cases hb'
    simpa only [hImage] using H
  · have hsub : S ⊆ I := by
      intro j hjS
      by_contra hjI
      exact hknown ⟨j, hjS, hjI⟩
    rw [hs0 I hsub a b k hI ha hb hk, ht0 I hsub a b k hI ha hb hk]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zeroGradedHom_heq (congrFun hobj a) (congrFun hobj b) k

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (ext_of_selected_faces_zero_unknown)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
