module
public import SerrePositivity.DifferentialGraded.Quotient.PrependTailNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality

/-! # 先頭Hom合成の後方自然性を表す全Hom写像の等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 後方tensor部分への作用と先頭Hom合成の可換式を全Homのchain mapとして保持する。 -/
lemma prependMap_tail_hom {S : Set D} (c : S) (w w' : Word S) (x y z : D) :
    (tensorLeftHom (homObject A D y c.val)
      (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
      tensorLeftHom (homObject A D x y) (term A D (c :: w) y z) (term A D (c :: w') y z)) ≫
      homPostcompose (homObject A D x y ⊗ term A D (c :: w) y z)
        (prependMap A D (c :: w') x y z) =
    tensorLeftHom (homObject A D x c.val)
      (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
      homPrecompose (prependMap A D (c :: w) x y z) (term A D (c :: w') x z) := by
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_hom_naturality (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) (epsilonComplex A ⊗ term A D w c.val z)
      (epsilonComplex A ⊗ term A D w' c.val z) (eComp (Complex A) x y c.val)

/-- ε因子を保持する操作も先に合成し、残るpathの全Homを始域とする。 -/
lemma prependMap_suffix_hom {S : Set D} (c : S) (w w' : Word S) (x y z : D) :
    tensorLeftHom (epsilonComplex A) (term A D w c.val z) (term A D w' c.val z) ≫
      ((tensorLeftHom (homObject A D y c.val)
        (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
        tensorLeftHom (homObject A D x y) (term A D (c :: w) y z) (term A D (c :: w') y z)) ≫
        homPostcompose (homObject A D x y ⊗ term A D (c :: w) y z)
          (prependMap A D (c :: w') x y z)) =
    tensorLeftHom (epsilonComplex A) (term A D w c.val z) (term A D w' c.val z) ≫
      (tensorLeftHom (homObject A D x c.val)
        (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
        homPrecompose (prependMap A D (c :: w) x y z) (term A D (c :: w') x z)) := by
  rw [prependMap_tail_hom]

end SerrePositivity.DifferentialGraded.DGQuotient
