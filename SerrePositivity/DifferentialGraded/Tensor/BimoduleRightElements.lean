module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements

/-! # bimodule合成の右作用の斉次生成元公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 右B作用は先頭Q因子の次数とのKoszul符号を伴ってP因子へ作用する。 -/
lemma compose_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b b' : Bᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A b b' p) (q : (Q.value c e).X k) (v : (P.value b.unop c).X r) :
    moduleAction A ((compose A B C E P Q).rightAt e) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v ha) hn =
    (p * k).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P.leftAt b'.unop) c q
      (moduleAction A (P.rightAt c) g v hj) (by omega) := by
  have he := BalancedTensor.leftHomMap_element_of_sum A C (Q.rightAt e) (l := j)
    ((P.transposeHom b b').f p g) c q v ha (by omega) hn
  have h := congrArg (fun z => z.f p g) (P.transposeHom_π b b' c)
  change (leftModuleHomπ A C (P.leftAt b.unop) (P.leftAt b'.unop) c).f p
    ((P.transposeHom b b').f p g) = ((P.rightAt c).map b b').f p g at h
  rw [h] at he
  exact he

end SerrePositivity.DifferentialGraded.BimoduleTensor
