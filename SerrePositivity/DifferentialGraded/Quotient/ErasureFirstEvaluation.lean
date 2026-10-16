module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureMiddleInterchange
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces

/-! # 先頭ε消去の標準生成元での成分式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭εを消すと、(-1)^i倍の先頭Hom合成になる。 -/
lemma eraseFirst_generator {S : Set D} (c : S) (w : Word S) (x y : D)
    (i j b a n : ℤ) (hb : (-1) + j = b) (ha : i + b = a) (hn : a + 1 = n)
    (f : (homObject A D x c.val).X i) (z : (term A D w c.val y).X j) :
    (eraseFirst A D c w x y).v a n hn
      (ιTensorObj (homObject A D x c.val) (epsilonComplex A ⊗ term A D w c.val y) i b a ha
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w c.val y) (-1) j b hb
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] z))) =
    i.negOnePow • (prependMap A D w x c.val y).f n
      (ιTensorObj (homObject A D x c.val) (term A D w c.val y) i j n (by omega)
        (f ⊗ₜ[A] z)) := by
  rw [eraseFirst, cochain_comp_ofHom_apply]
  exact (congrArg (fun t => (prependMap A D w x c.val y).f n t)
    (eraseMiddle_generator A (homObject A D x c.val) (term A D w c.val y)
      i j b a n hb ha hn f z)).trans
    (chain_units_smul (prependMap A D w x c.val y) n i.negOnePow _)

end SerrePositivity.DifferentialGraded.DGQuotient
