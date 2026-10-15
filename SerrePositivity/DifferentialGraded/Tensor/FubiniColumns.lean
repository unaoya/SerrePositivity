module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniFamilies
public import SerrePositivity.DifferentialGraded.Tensor.FubiniRightAction
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 二重balanced族のE方向のパラメータ付き降下 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

omit [Small.{u} E] in
/-- 外側のbalanced関係を、内側の二つの和次数を明示して用いる。 -/
lemma DoubleFamily.balanceE_of_sums {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c : C) (e e' : E) {k p r s j i n : ℤ}
    (hj : r + p = j) (hi : j + s = i) (hn : k + p + (r + s) = n)
    (t : (R.obj (op e')).X k) (f : GradedHom A e e' p)
    (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    (k * p).negOnePow • tripleElement A C E (n := n)
      (fun c e => (a.row e).val c) c e (moduleAction A R f t rfl) q v rfl (by omega) =
    tripleElement A C E (n := n) (fun c e => (a.row e).val c) c e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) f q hj) v hi (by omega) := by
  subst j i
  exact a.balanceE c e e' k p r s n hn t f q v

/-- Cの対象を固定し、右にN(c)を置いたchain map族。 -/
def columnMaps {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    (R.obj (op e) ⊗ Q.value c e) ⊗ N.obj c ⟶ T :=
  (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).hom ≫ (a.row e).val c

omit [Small.{u} E] in
/-- N(c)を終域へ転置したE方向の族はbalancedである。 -/
def columnCurry {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    BalancedFamily A E R (Q.leftAt c) (homComplex A (N.obj c) T) := by
  refine balancedFamilyMk A E (fun e => curryRight (columnMaps A C E a c e)) ?_
  intro e e' k p r n hn t f q
  apply Cochain.ext
  intro s m hm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v]
  change (k * p).negOnePow •
    (columnMaps A C E a c e).f m
      (ιTensorObj (R.obj (op e) ⊗ Q.value c e) (N.obj c) n s m (by omega)
        (ιTensorObj (R.obj (op e)) (Q.value c e) (k + p) r n hn
          (moduleAction A R f t rfl ⊗ₜ[A] q) ⊗ₜ[A] v)) =
    (columnMaps A C E a c e').f m
      (ιTensorObj (R.obj (op e') ⊗ Q.value c e') (N.obj c) n s m (by omega)
        (ιTensorObj (R.obj (op e')) (Q.value c e') k (p + r) n (by omega)
          (t ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c)
            (n := p + r) f q (by omega)) ⊗ₜ[A] v))
  simp only [columnMaps, comp_f, ModuleCat.comp_apply]
  rw [associator_apply_of_sums _ _ _ (k + p) r s n (r + s) m hn rfl (by omega),
    associator_apply_of_sums _ _ _ k (p + r) s n (p + r + s) m (by omega) rfl (by omega)]
  exact a.balanceE_of_sums A C E c e e' (j := p + r) (i := p + r + s)
    (by omega) rfl (by omega) t f q v

/-- 右パラメータ付き族のbalanced条件を転置から復元する。 -/
def columnFamily {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    RightParamFamily A E R (Q.leftAt c) (N.obj c) T := by
  refine ⟨columnMaps A C E a c, ?_⟩
  intro e e'
  apply (tensorRightHomEquiv (N.obj c) _ T).injective
  change curryRight (((rightAction A E R e e' ▷ (Q.leftAt c).obj e) ⊗ₘ 𝟙 (N.obj c)) ≫
    columnMaps A C E a c e) =
    curryRight ((((α_ (R.obj (op e')) (e ⟶[Complex A] e') ((Q.leftAt c).obj e)).hom ≫
      R.obj (op e') ◁ leftAction A E (Q.leftAt c) e e') ⊗ₘ 𝟙 (N.obj c)) ≫
        columnMaps A C E a c e')
  rw [curryRight_naturality_source, curryRight_naturality_source]
  exact (columnCurry A C E a c).property e e'

/-- 二重balanced族をEに関して降ろした射。 -/
def columnDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    (rightModule A C E Q R).obj (op c) ⊗ N.obj c ⟶ T :=
  rightParamDesc A E R (Q.leftAt c) (columnFamily A C E a c)

@[reassoc (attr := simp)]
lemma ι_columnDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ columnDesc A C E a c = columnMaps A C E a c e :=
  ι_rightParamDesc A E R (Q.leftAt c) (columnFamily A C E a c) e

/-- E方向の降下を斉次三重生成元で計算する。 -/
lemma columnDesc_element {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E)
    {k r s l n : ℤ} (hl : k + r = l) (hn : l + s = n)
    (t : (R.obj (op e)).X k) (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    (columnDesc A C E a c).f n
      (ιTensorObj ((rightModule A C E Q R).obj (op c)) (N.obj c) l s n hn
        (element A E R (Q.leftAt c) e t q hl ⊗ₜ[A] v)) =
    tripleElement A C E (fun c e => (a.row e).val c) c e t q v rfl (by omega) := by
  have h := rightParamDesc_element A E R (Q.leftAt c) (columnFamily A C E a c)
    e hl hn t q v
  change _ = (columnMaps A C E a c e).f n
    (ιTensorObj (R.obj (op e) ⊗ Q.value c e) (N.obj c) l s n hn
      (ιTensorObj (R.obj (op e)) (Q.value c e) k r l hl (t ⊗ₜ[A] q) ⊗ₜ[A] v)) at h
  simp only [columnMaps, comp_f, ModuleCat.comp_apply] at h
  rw [associator_apply_of_sum _ _ _ k r s l n hl hn] at h
  exact h

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
