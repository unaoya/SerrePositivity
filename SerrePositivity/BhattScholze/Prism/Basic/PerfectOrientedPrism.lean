module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular

/-! # 完全oriented prismの生成元と射

著者公開版Lemma 3.5・Theorem 3.10の主イデアルの場合。
実導来完備性から正則元の古典的完備性へ共通比較を適用し、
distinguished生成元・有界p冪ねじれ・射によるイデアル像を証明する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全oriented prismの古典的p進完備性。 -/
theorem isAdicComplete_p_of_perfect (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : IsAdicComplete (Ideal.span {(p : A)}) A :=
  P.isAdicComplete_p_of_regular hP.p_mul_injective

/-- 完全oriented prismの選択生成元はdistinguished。 -/
theorem isDistinguished_of_perfect (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : P.deltaStructure.IsDistinguished P.generator :=
  P.isDistinguished_of_p_regular hP.p_mul_injective

/-- 完全oriented prismの商のp冪ねじれはpで消える。
原典のbounded性の具体的な評価N=1。 -/
theorem quotient_p_pow_torsion_killed_by_p (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) (n : ℕ) (x : A ⧸ P.ideal)
    (hx : (p : A ⧸ P.ideal) ^ n * x = 0) : (p : A ⧸ P.ideal) * x = 0 :=
  hP.distinguished_quotient_p_pow_torsion_killed_by_p (P.isDistinguished_of_perfect hP) n x hx

/-- p進・d進完備な完全δ環のdistinguished元は、実導来条件を持つoriented prismを与える。
古典的完備性から導来完備性への既存共通定理を明示的に使用する。 -/
def ofPerfectCompleteDistinguished (D : DeltaStructure p A) (hD : D.IsPerfect)
    (d : A) (hd : D.IsDistinguished d)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [IsAdicComplete (Ideal.span {d}) A] :
    OrientedPrism p A :=
  ofDistinguished D d hd (hD.distinguished_mul_injective hd)
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A d (ModuleCat.of A A))

/-- 完全oriented prism間のδ射が生成元を終域のイデアルへ送れば、
イデアルの像は終域のイデアル全体。Lemma 3.5の主イデアルの場合。 -/
theorem map_ideal_eq_of_perfect {B : Type v} [CommRing B]
    (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : P.deltaStructure.IsDeltaHom Q.deltaStructure f)
    (hI : f P.generator ∈ Q.ideal) : P.ideal.map f = Q.ideal := by
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_perfect hQ
  exact hf.map_span_eq_of_distinguished_of_mem_span (P.isDistinguished_of_perfect hP) hI
    (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B)}) (Ideal.subset_span (by simp)))

end SerrePositivity.BhattScholze.OrientedPrism
