module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalElements
public import SerrePositivity.KST.SConstruction.DGFunctorHomElements

/-! # 横合成と縦合成の全次数交換律
概要：元の斉次自然変換の横合成が縦合成と交換する際の Koszul 符号を証明する。
方針：全対象で評価し、中間の二成分だけを全次数自然性で交換する。
規約：交差する二次数の符号を保持する。使われ方：横合成の dg 合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

private lemma forward_smul_left {A : Type u} [CommRing A] {E : Type*} [DGCategory A E]
    {x y z : E} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (hn : p + q = n) (c : ℤˣ) : forward A (c • f) g hn = c • forward A f g hn := by
  simp only [forward, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]

private lemma forward_smul_right {A : Type u} [CommRing A] {E : Type*} [DGCategory A E]
    {x y z : E} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (hn : p + q = n) (c : ℤˣ) : forward A f (c • g) hn = c • forward A f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

/-- 斉次四重合成で、中間二射の符号つき交換を全体へ移す。 -/
lemma dgMiddleInterchange {A : Type u} [CommRing A] {E : Type*} [DGCategory A E]
    {x₀ x₁ x₂ x₁' x₃ x₄ : E} {p q r s n : ℤ}
    (a : GradedHom A x₀ x₁ p) (b : GradedHom A x₁ x₂ q)
    (c : GradedHom A x₂ x₃ r) (d : GradedHom A x₃ x₄ s)
    (c' : GradedHom A x₁ x₁' r) (b' : GradedHom A x₁' x₃ q) (sign : ℤˣ)
    (h : forward A b c rfl = sign • forward A c' b' (by omega))
    (hn : (p + q) + (r + s) = n) :
    forward A (forward A a b rfl) (forward A c d rfl) hn =
      sign • forward A (forward A a c' rfl) (forward A b' d rfl) (by omega) := by
  rw [forward_assoc_of_sum A a b (forward A c d rfl)
      (a := p + q) (b := q + (r + s)) rfl rfl hn,
    ← forward_assoc_of_sum A b c d (a := q + r) (b := r + s)
      (n := q + (r + s)) rfl rfl (by omega),
    h, forward_smul_left, forward_smul_right,
    forward_assoc_of_sum A c' b' d (a := q + r) (b := q + s)
      (n := q + (r + s)) (by omega) rfl (by omega),
    ← forward_assoc_of_sum A a c' (forward A b' d rfl)
      (a := p + r) (b := q + (r + s)) rfl (by omega) (by omega)]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]

/-- 全次数の横合成は、交差する中間二次数の符号を保って縦合成と交換する。 -/
lemma dgFunctorHorizontalElement_interchange
    {F₀ F₁ F₂ : DGFunctor A D E} {G₀ G₁ G₂ : DGFunctor A E B} {p q r s n : ℤ}
    (a : GradedHom A F₀ F₁ p) (b : GradedHom A G₀ G₁ q)
    (c : GradedHom A F₁ F₂ r) (d : GradedHom A G₁ G₂ s)
    (hn : (p + q) + (r + s) = n) :
    forward A (dgFunctorHorizontalElement A D E B a b rfl)
        (dgFunctorHorizontalElement A D E B c d rfl) hn =
      (q * r).negOnePow • dgFunctorHorizontalElement A D E B
        (forward A a c rfl) (forward A b d rfl) (by omega) := by
  apply dgFunctorHomElement_ext A D B
  intro x
  simp only [dgFunctorHomπ_forward, dgFunctorHorizontalElement_π,
    Units.smul_def, map_zsmul, DGFunctor.map_forward]
  exact dgMiddleInterchange _ _ _ _ _ _ _
    (dgFunctorHomElement_naturality A E B b
      ((dgFunctorHomπ A D E F₁ F₂ x).f r c) rfl).symm hn

end SerrePositivity.KST.SConstruction
