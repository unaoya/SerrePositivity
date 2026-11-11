module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBoundary
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
/-!
概要：次数 −1 の実比較 cochain の微分式を、全整数次数の実成分へ移す。
方針：同じ全 cochain 等式を評価し、既存 δ_v の式を使う。
規約：閉次数零射に限定しない。使われ方：augmentation の全高次 prism の符号照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 全比較微分式は、各次数で同じ二項の実鎖ホモトピー式になる。 -/
lemma complexMinusOneCochain_boundary_v {P Q : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0) (n : ℤ) :
    h.v n (n - 1) (by omega) ≫ Q.d (n - 1) n +
      P.d n (n + 1) ≫ h.v (n + 1) n (by omega) + f.f n = 0 := by
  have he := Cochain.congr_v hh n n (add_zero n)
  rw [Cochain.add_v, δ_v (-1) 0 (by omega) h n n (add_zero n)
    (n - 1) (n + 1) rfl rfl] at he
  simpa only [Int.negOnePow_zero, one_smul, Cochain.ofHom_v, Cochain.zero_v] using he
/-- 同じ実 cochain を斉次元に評価しても、全微分式を保つ。 -/
lemma complexMinusOneCochain_boundary_apply {P Q : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0)
    (n : ℤ) (a : P.X n) :
    Q.d (n - 1) n (h.v n (n - 1) (by omega) a) +
      h.v (n + 1) n (by omega) (P.d n (n + 1) a) + f.f n a = 0 :=
  ConcreteCategory.congr_hom (complexMinusOneCochain_boundary_v h f hh n) a
/-- 閉次数零元では、同じ比較 cochain の微分が実比較差の負になる。 -/
lemma complexMinusOneCochain_boundary_closed_zero {P Q : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0)
    (a : P.X 0) (ha : P.d 0 1 a = 0) :
    Q.d (-1) 0 (h.v 0 (-1) (by omega) a) = - f.f 0 a := by
  have he := complexMinusOneCochain_boundary_apply h f hh 0 a
  change Q.d (-1) 0 (h.v 0 (-1) (by omega) a) +
    h.v 1 0 (by omega) (P.d 0 1 a) + f.f 0 a = 0 at he
  rw [ha, map_zero, add_zero] at he
  exact eq_neg_of_add_eq_zero_left he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
