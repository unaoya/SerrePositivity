module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceExtensionality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Replace

/-! # dg 単体データの全ての面と最上位による同定

概要：全面が一致するデータは真部分集合の成分で一致し、最上位も一致すれば等しい。
方針：既知成分はそれを含む面で比較する。右辺は最上位の零置換で比較する。
規約：端点の対象表示の差は異種等号で扱う。使われ方：β3 の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 全ての面は頂点全体を覆う。 -/
lemma allFacesCoverVertices (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (Finset.univ : Finset (Fin (n + 2))) := by
  intro k
  obtain ⟨j, hj⟩ := exists_ne k
  exact ⟨j, Finset.mem_univ j, hj⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (allFacesCoverVertices)


/-- 全面の一致から、任意の真部分集合の斉次成分は異種等号で一致する。 -/
lemma hom_heq_of_all_faces {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hfaces : ∀ j : Fin (n + 2), s.pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hne : I ≠ Finset.univ) :
    HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk) := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
    simpa only [ne_eq, Finset.eq_univ_iff_forall, not_forall] using hne
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
    j.succAboveOrderEmb.toOrderHom (hfaces j) J a' b' k hJ rfl rfl
    (by rw [hcard]; exact hk) j.succAboveOrderEmb.injective.injOn
    j.succAboveOrderEmb.injective.injOn
  cases ha'
  cases hb'
  simpa only [hImage] using H

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (hom_heq_of_all_faces)


/-- 全ての面と最上位の成分の一致は単体データ全体の一致を与える。 -/
lemma ext_of_all_faces_and_top {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hfaces : ∀ j : Fin (n + 2), s.pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom)
    (htop : ∀ a b k hI ha hb hk,
      HEq (s.hom Finset.univ a b k hI ha hb hk) (t.hom Finset.univ a b k hI ha hb hk)) : s = t := by
  have hobj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.obj_eq_of_selected_faces Finset.univ (allFacesCoverVertices n) s t
    (fun j _ => hfaces j)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  by_cases hfull : I = Finset.univ
  · subst I
    exact htop a b k hI ha hb hk
  · exact hom_heq_of_all_faces s t hfaces I a b k hI ha hb hk hfull

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (ext_of_all_faces_and_top)


/-- 等しいデータの方程式の右辺は端点の表示も含め異種等号で一致する。 -/
lemma rhs_heq_of_eq {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n} (h : s = t)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    HEq (s.rhs I a b k hI ha hb hk) (t.rhs I a b k hI ha hb hk) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (rhs_heq_of_eq)


/-- 全面が一致すれば、最上位の方程式の右辺は異種等号で一致する。 -/
lemma rhs_heq_of_all_faces {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (hfaces : ∀ j : Fin (n + 2), s.pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    HEq (s.rhs Finset.univ a b k hI ha hb hk) (t.rhs Finset.univ a b k hI ha hb hk) := by
  let fs := fun (a b : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (_ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (_hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (_hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) =>
      (0 : GradedHom A (s.obj a) (s.obj b) k)
  let ft := fun (a b : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (_ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (_hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (_hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) =>
      (0 : GradedHom A (t.obj a) (t.obj b) k)
  have he : s.replace Finset.univ fs = t.replace Finset.univ ft := by
    apply ext_of_all_faces_and_top
    · intro j
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits s _ _ _ j (Finset.mem_univ j) (Fin.succAbove_ne j),
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits t _ _ _ j (Finset.mem_univ j) (Fin.succAbove_ne j)]
      exact hfaces j
    · intro a b k hI ha hb hk
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same]
      have hobj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.obj_eq_of_selected_faces Finset.univ (allFacesCoverVertices n) s t
        (fun j _ => hfaces j)
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zeroGradedHom_heq (congrFun hobj a) (congrFun hobj b) k
  have hh := rhs_heq_of_eq he Finset.univ a b k hI ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replace_self, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replace_self] at hh
  exact hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (rhs_heq_of_all_faces)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
