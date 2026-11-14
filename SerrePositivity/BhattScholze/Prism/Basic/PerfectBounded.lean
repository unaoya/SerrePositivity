module

public import SerrePositivity.BhattScholze.Prism.Basic.Bounded
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Bounded

/-!
# 完全 prism の有界性と生成元

BS 著者版 Lemma 3.8 (1)(2) の向き付きの場合。
任意の生成元の distinguished 性と、剰余環のねじれの上界1を既存の δ 環の補題から得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- BS 著者版 Lemma 3.8 (1) の生成元の条件。
prism イデアルの任意の生成元が distinguished。選択生成元との主イデアルの一致と
Jacobson 根基への包含を用い、完全性の仮定は不要。 -/
theorem OrientedPrism.isDistinguished_of_span_eq (P : OrientedPrism p A) {d : A}
    (hd : Ideal.span {d} = P.ideal) : P.deltaStructure.IsDistinguished d := by
  have hle : P.ideal ≤ Ideal.jacobson (⊥ : Ideal A) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr P.generator_mem_jacobson)
  have hdj : d ∈ Ideal.jacobson (⊥ : Ideal A) :=
    hle (hd ▸ Ideal.mem_span_singleton_self d)
  exact (P.deltaStructure.isDistinguished_iff_of_span_eq d P.generator hdj
    P.generator_mem_jacobson P.p_mem_jacobson hd).mpr P.isDistinguished_generator

namespace Prismatic

/-- BS 著者版 Definition 3.2 の有界性は剰余環の有界な p 冪ねじれ。
既存の定義式を変更せず、新しい述語との定義的な一致を表す。 -/
theorem isBoundedPrism_iff_hasBoundedPTorsion (P : OrientedPrism p A) :
    IsBoundedPrism P ↔ HasBoundedPTorsion p (A ⧸ P.ideal) := Iff.rfl

/-- BS 著者版 Lemma 3.8 (2)：完全 prism は有界。
選択生成元は distinguished であり、完全 δ 環の distinguished 商のねじれは p で消える。
有界性の一様な指数として1を選ぶ。 -/
theorem isBoundedPrism_of_perfect (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    IsBoundedPrism P := by
  refine ⟨1, fun n x hx => ?_⟩
  simpa only [pow_one] using P.quotient_p_pow_torsion_killed_by_p hP n x hx

end Prismatic
end SerrePositivity.BhattScholze
