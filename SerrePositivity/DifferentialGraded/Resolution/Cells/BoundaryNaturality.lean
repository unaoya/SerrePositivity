module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHead
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality

/-! # 全位置の境界置換と既存Hom作用の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma replaceFace_nil (j : ℕ) (x y : D) : C.replaceFace A D I [] j x y = 0 := rfl

lemma replaceFace_zero (i : I) (w : List I) (x y : D) :
    C.replaceFace A D I (i :: w) 0 x y = C.replaceFirst A D I i w x y := rfl

lemma replaceFace_succ (i : I) (w : List I) (j : ℕ) (x y : D) :
    C.replaceFace A D I (i :: w) (j + 1) x y =
    (tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      ((tensorLeftHom (C.generator A D I i) _ _).f 1
        (C.replaceFace A D I w j (C.target i) y)) := rfl

attribute [local irreducible] replaceFace

lemma prependMap_tail_hom (i : I) (w w' : List I) (x y z : D) :
    (tensorLeftHom (homObject A D y (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
      tensorLeftHom (homObject A D x y) (C.term A D I (i :: w) y z)
        (C.term A D I (i :: w') y z)) ≫
      homPostcompose (homObject A D x y ⊗ C.term A D I (i :: w) y z)
        (C.prependMap A D I (i :: w') x y z) =
    tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
      homPrecompose (C.prependMap A D I (i :: w) x y z) (C.term A D I (i :: w') x z) := by
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_hom_naturality (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ (eComp (Complex A) x y (C.source i))

lemma prependMap_suffix_hom (i : I) (w w' : List I) (x y z : D) :
    tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) z)
      (C.term A D I w' (C.target i) z) ≫
      ((tensorLeftHom (homObject A D y (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
        (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
        tensorLeftHom (homObject A D x y) (C.term A D I (i :: w) y z)
          (C.term A D I (i :: w') y z)) ≫
        homPostcompose (homObject A D x y ⊗ C.term A D I (i :: w) y z)
          (C.prependMap A D I (i :: w') x y z)) =
    tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) z)
      (C.term A D I w' (C.target i) z) ≫
      (tensorLeftHom (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
        (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) ≫
        homPrecompose (C.prependMap A D I (i :: w) x y z) (C.term A D I (i :: w') x z)) := by
  rw [prependMap_tail_hom]

lemma prependMap_replaceFace (w : List I) (j : ℕ) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp
      (C.replaceFace A D I w j x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1 (C.replaceFace A D I w j y z)).comp
      (Cochain.ofHom (C.prependMap A D I (w.eraseIdx j) x y z)) (add_zero 1) := by
  cases w with
  | nil => simp only [replaceFace_nil, map_zero, Cochain.comp_zero, Cochain.zero_comp]
  | cons i w =>
    cases j with
    | zero =>
      rw [replaceFace_zero, replaceFace_zero]
      exact C.prependMap_replaceFirst A D I i w x y z
    | succ j =>
      have h := congrArg (fun t : homComplex A (C.term A D I w (C.target i) z)
          (C.term A D I (w.eraseIdx j) (C.target i) z) ⟶
          homComplex A (homObject A D x y ⊗ C.term A D I (i :: w) y z)
            (C.term A D I (i :: w.eraseIdx j) x z) =>
          t.f 1 (C.replaceFace A D I w j (C.target i) z))
        (C.prependMap_suffix_hom A D I i w (w.eraseIdx j) x y z)
      simp only [chain_comp_apply, homPostcompose_apply] at h
      rw [replaceFace_succ, replaceFace_succ]
      exact h.symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
