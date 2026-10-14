module
public import SerrePositivity.DifferentialGraded.Complexes.ShiftCoherence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # 閉零射の cone に作用する全次数対角 cochain

cone の左成分は +1 shift なので、次数 p の作用に (-1)^p が入る。
Mathlib の mappingCone とその射影・包含を再利用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {P Q R S : Complex A}

/-- 二つの斉次射を cone 上の符号付き対角 cochain にする。 -/
def coneMapCochain (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    Homogeneous (mappingCone f) (mappingCone g) p :=
  mappingCone.liftCochain g
    (p.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + p = p + 1))
    ((mappingCone.snd f).comp b (zero_add p)) rfl

/-- 第一射影後の cone 作用は shift の Koszul 符号を持つ。 -/
lemma coneMapCochain_fst (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (coneMapCochain f g a b).comp (mappingCone.fst g).val rfl =
      p.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + p = p + 1) :=
  mappingCone.liftCochain_fst _ _ _ _

/-- 第二射影後の cone 作用は第二成分の作用。 -/
lemma coneMapCochain_snd (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (coneMapCochain f g a b).comp (mappingCone.snd g) (add_zero p) =
      (mappingCone.snd f).comp b (zero_add p) :=
  mappingCone.liftCochain_snd _ _ _ _

/-- 全斉次次数の cone 作用の成分公式。 -/
lemma coneMapCochain_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij =
      p.negOnePow • ((mappingCone.fst f).val.v i (i + 1) rfl ≫
        a.v (i + 1) (j + 1) (by omega) ≫
          (mappingCone.inl g).v (j + 1) j (by omega)) +
      (mappingCone.snd f).v i i (add_zero i) ≫ b.v i j hij ≫ (mappingCone.inr g).f j := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.add_v,
    Cochain.comp_v _ _ (by omega : (p + 1) + (-1) = p) i (j + 1) j (by omega) (by omega),
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.units_smul_v, Cochain.ofHom_v,
    Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) (j + 1) rfl (by omega),
    Linear.units_smul_comp, Category.assoc]

/-- 対角 cone 作用は加法を保存する。 -/
lemma coneMapCochain_add (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a a' : Homogeneous P R p) (b b' : Homogeneous Q S p) :
    coneMapCochain f g (a + a') (b + b') =
      coneMapCochain f g a b + coneMapCochain f g a' b' := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_add, smul_add,
    Cochain.add_comp]
  abel

/-- 対角 cone 作用は係数環のスカラー倍を保存する。 -/
lemma coneMapCochain_smul (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) (r : A) :
    coneMapCochain f g (r • a) (r • b) = r • coneMapCochain f g a b := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_smul,
    Cochain.smul_comp, smul_add]
  rw [smul_comm p.negOnePow r]
  simp only [Cochain.smul_comp]

/-- 対角 cone 作用は整数単位の符号倍を保存する。 -/
lemma coneMapCochain_units_smul (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) (r : ℤˣ) :
    coneMapCochain f g (r • a) (r • b) = r • coneMapCochain f g a b := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_units_smul,
    Cochain.units_smul_comp, smul_add]
  rw [smul_comm p.negOnePow r]

/-- 次数零の恒等対角作用は cone の恒等 cochain。 -/
lemma coneMapCochain_identity (f : P ⟶ Q) :
    coneMapCochain f f (Cochain.ofHom (𝟙 P)) (Cochain.ofHom (𝟙 Q)) =
      Cochain.ofHom (𝟙 (mappingCone f)) := by
  apply (mappingCone.ext_cochain_to_iff f 0 1 rfl).2
  constructor
  · rw [coneMapCochain_fst]
    simp only [Int.negOnePow_zero, one_smul, Cochain.comp_id, Cochain.id_comp]
  · rw [coneMapCochain_snd]
    simp only [Cochain.comp_id, Cochain.id_comp]

/-- 可換な斉次 square に対して、cone 対角作用は Hom 微分と可換。 -/
lemma coneMapCochain_differential (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (h : a.comp (Cochain.ofHom g) (add_zero p) =
      (Cochain.ofHom f).comp b (zero_add p)) :
    δ p (p + 1) (coneMapCochain f g a b) =
      coneMapCochain f g (δ p (p + 1) a) (δ p (p + 1) b) := by
  unfold coneMapCochain
  rw [mappingCone.δ_liftCochain g _ _ rfl (p + 1 + 1) rfl]
  rw [δ_units_smul, δ_comp (mappingCone.fst f).val a (by omega : 1 + p = p + 1)
    2 (p + 1) (p + 1 + 1) rfl rfl rfl]
  simp only [Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero]
  rw [δ_comp (mappingCone.snd f) b (zero_add p) 1 (p + 1) (p + 1) rfl
    (zero_add 1) rfl, mappingCone.δ_snd]
  simp only [Cochain.units_smul_comp,
    Cochain.neg_comp, smul_neg]
  rw [Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, h]
  simp only [add_assoc, neg_add_cancel, add_zero]
  simp only [mappingCone.liftCochain, Int.negOnePow_succ, Units.neg_smul,
    Cochain.neg_comp, Cochain.units_smul_comp]

/-- 対角 cone 作用は通常順の全斉次合成を保存する。 -/
lemma coneMapCochain_comp {T U : Complex A}
    (f : P ⟶ Q) (g : R ⟶ S) (h : T ⟶ U) {p q n : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (c : Homogeneous R T q) (d : Homogeneous S U q) (hn : p + q = n) :
    (coneMapCochain f g a b).comp (coneMapCochain g h c d) hn =
      coneMapCochain f h (a.comp c hn) (b.comp d hn) := by
  apply (mappingCone.ext_cochain_to_iff h n (n + 1) rfl).2
  constructor
  · rw [Cochain.comp_assoc _ _ _ hn rfl (by omega), coneMapCochain_fst,
      Cochain.comp_units_smul]
    rw [← Cochain.comp_assoc _ _ _ rfl (by omega : 1 + q = q + 1) (by omega),
      coneMapCochain_fst, Cochain.units_smul_comp,
      Cochain.comp_assoc _ _ _ (by omega : 1 + p = p + 1) hn (by omega),
      coneMapCochain_fst, smul_smul, ← Int.negOnePow_add]
    congr 1
    congr 1
    omega
  · rw [Cochain.comp_assoc_of_third_is_zero_cochain, coneMapCochain_snd,
      ← Cochain.comp_assoc_of_second_is_zero_cochain, coneMapCochain_snd,
      Cochain.comp_assoc_of_first_is_zero_cochain, coneMapCochain_snd]

/-- cone の標準包含は全次数対角作用と可換。 -/
lemma coneMapCochain_inr (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (Cochain.ofHom (mappingCone.inr f)).comp (coneMapCochain f g a b) (zero_add p) =
      b.comp (Cochain.ofHom (mappingCone.inr g)) (add_zero p) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v, coneMapCochain_v]
  simp only [Preadditive.comp_add, Linear.comp_units_smul,
    mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
    zero_comp, smul_zero, zero_add]
end SerrePositivity.DifferentialGraded
