module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainAction

/-! # 結合比較のRight作用の三重生成元上の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 右B作用のKoszul符号は結合比較の両側で一致する。 -/
lemma associatorComponent_rightCochain_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    associatorValueComponent A B C E F P Q R b'.unop f n
      ((associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn
        (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)) =
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorValueComponent A B C E F P Q R b.unop f m
        (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)) := by
  have hkrm : (k + r) + s = m :=
    (add_assoc k r s).trans ((congrArg (fun z : ℤ => k + z) hi).trans hm)
  have hri : r + (s + p) = i + p :=
    (add_assoc r s p).symm.trans (congrArg (fun z : ℤ => z + p) hi)
  have hki : k + (i + p) = n :=
    (add_assoc k i p).symm.trans ((congrArg (fun z : ℤ => z + p) hm).trans hn)
  have hkrsp : (k + r) + (s + p) = n :=
    (add_assoc (k + r) s p).symm.trans ((congrArg (fun z : ℤ => z + p) hkrm).trans hn)
  let v' := moduleAction A (P.rightAt c) (n := s + p) g v rfl
  let x₀ := associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm
  let x₁ := associatorLeftElement A B C E F P Q R b'.unop c e f (i := i + p) (n := n)
    t q v' hri hki
  let y₀ := associatorRightElement A B C E F P Q R b.unop c e f (l := k + r) (n := m)
    t q v rfl hkrm
  let y₁ := associatorRightElement A B C E F P Q R b'.unop c e f (l := k + r) (n := n)
    t q v' rfl hkrsp
  let σ : ℤˣ := (p * (k + r)).negOnePow
  have hL := associatorLeft_rightAction_element A B C E F P Q R b b' c e f
    (j := s + p) (i' := i + p) hi hm rfl rfl hn g t q v
  have hR := associatorRight_rightAction_element A B C E F P Q R b b' c e f
    (l := k + r) (j := s + p) rfl hkrm rfl hn g t q v
  have hS := associatorValueComponent_element A B C E F P Q R b.unop c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hM := associatorValueComponent_element A B C E F P Q R b'.unop c e f
    (i := i + p) (l := k + r) (n := n) t q v' hri rfl hki
  have hLP := associatorLeftBCochain_apply A B C E F P Q R b b' f g x₀ hn
  have hRP := associatorRightBCochain_apply A B C E F P Q R b b' f g y₀ hn
  have hσ := chain_units_smul (associatorValueHom A B C E F P Q R b'.unop f) n σ x₁
  simp only [associatorValueHom_apply] at hσ
  have hMσ := hσ.trans (congrArg (fun z => σ • z) hM)
  exact element_square
    (fun z => associatorValueComponent A B C E F P Q R b.unop f m z)
    (fun z => associatorValueComponent A B C E F P Q R b'.unop f n z)
    (fun z => (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn z)
    (fun z => (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn z)
    x₀ (σ • x₁) y₀ (σ • y₁) (hLP.trans hL) hS hMσ (hRP.trans hR)

end SerrePositivity.DifferentialGraded.BimoduleTensor
