module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexShift
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-!
# 一般の線形加法圏の写像複体と cone の比較

概要：Hom(X,cone(f)) を Hom(X,f) の cone で具体的に表示する。
方針：cone の二つの射影と Mathlib の liftCochain の微分公式を使う。
規約：有界性・平坦性を要求せず、実際の chain map とその逆を比較する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：通常の chain map による写像複体の後合成。
方針：各 cochain を後合成し、δ_comp_zero_cochain で微分と比較する。
規約：対象圏は任意の線形加法圏。
使われ方：Drinfeld §2.4、KST D4 の cone の写像複体。
-/
def mappingPostcompose (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    mappingComplex A X Y ⟶ mappingComplex A X Z :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom
      { toFun g := g.comp (Cochain.ofHom f) (add_zero q)
        map_add' g h := Cochain.add_comp g h _ _
        map_smul' a g := Cochain.smul_comp a g _ _ })
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      change δ q (q + 1) (g.comp (Cochain.ofHom f) (add_zero q)) =
        (δ q (q + 1) g).comp (Cochain.ofHom f) (add_zero (q + 1))
      rw [δ_comp_zero_cochain g (Cochain.ofHom f) (q + 1) rfl,
        δ_ofHom, Cochain.comp_zero, zero_add])

variable [HasBinaryBiproducts C]

/--
概要：二つの cochain から cone へ入る cochain を作る線形写像。
方針：liftCochain の合成の加法性と線形性を使う。
規約：第一成分の次数は第二成分より一つ高い。
使われ方：Drinfeld §2.4、KST D4 の cone の写像複体。
-/
def coneLiftLinearMap (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ}
    (f : Y ⟶ Z) (q : ℤ) :
    (Cochain X Y (q + 1) × Cochain X Z q) →ₗ[A] Cochain X (mappingCone f) q where
  toFun z := mappingCone.liftCochain f z.1 z.2 rfl
  map_add' z w := by
    change mappingCone.liftCochain f (z.1 + w.1) (z.2 + w.2) rfl = _
    simp only [mappingCone.liftCochain, Cochain.add_comp]
    abel
  map_smul' a z := by
    change mappingCone.liftCochain f (a • z.1) (a • z.2) rfl = _
    simp only [mappingCone.liftCochain, Cochain.smul_comp, smul_add, RingHom.id_apply]

/--
概要：写像複体上の cone の元を、元の cone へ入る cochain に送る線形写像。
方針：第一射影と第二射影を liftCochain で組み立てる。
規約：第一成分の次数は第二成分より一つ高い。
使われ方：Drinfeld §2.4、KST D4 の cone の具体的比較。
-/
def mappingConeComponent (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ}
    (f : Y ⟶ Z) (q : ℤ) :
    (mappingCone (mappingPostcompose A X f)).X q ⟶ (mappingComplex A X (mappingCone f)).X q :=
  ModuleCat.ofHom ((coneLiftLinearMap A X f q).comp
    (((mappingCone.fst (mappingPostcompose A X f)).val.v q (q + 1) rfl).hom.prod
      ((mappingCone.snd (mappingPostcompose A X f)).v q q (add_zero q)).hom))

/--
概要：cone の第一射影と微分の具体的な符号公式。
方針：Mathlib の d_fst_v を元で評価する。
規約：第一成分の微分には負号が付く。
使われ方：Drinfeld §2.4、KST D4 の cone 比較の chain 条件。
-/
lemma mappingCone_fst_d (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ}
    (f : Y ⟶ Z) (q : ℤ) (z : (mappingCone (mappingPostcompose A X f)).X q) :
    (mappingCone.fst (mappingPostcompose A X f)).val.v (q + 1) (q + 1 + 1) rfl
      ((mappingCone (mappingPostcompose A X f)).d q (q + 1) z) =
    -δ (q + 1) (q + 1 + 1)
      ((mappingCone.fst (mappingPostcompose A X f)).val.v q (q + 1) rfl z) := by
  have h := congrArg (fun g => g z)
    (mappingCone.d_fst_v (mappingPostcompose A X f) q (q + 1) (q + 1 + 1) rfl rfl)
  exact h

/--
概要：cone の第二射影と微分の具体的な公式。
方針：Mathlib の d_snd_v を元で評価する。
規約：第一成分の像と第二成分の微分を足す。
使われ方：Drinfeld §2.4、KST D4 の cone 比較の chain 条件。
-/
lemma mappingCone_snd_d (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ}
    (f : Y ⟶ Z) (q : ℤ) (z : (mappingCone (mappingPostcompose A X f)).X q) :
    (mappingCone.snd (mappingPostcompose A X f)).v (q + 1) (q + 1) (add_zero _)
      ((mappingCone (mappingPostcompose A X f)).d q (q + 1) z) =
      ((mappingCone.fst (mappingPostcompose A X f)).val.v q (q + 1) rfl z).comp
        (Cochain.ofHom f) (add_zero _) +
      δ q (q + 1) ((mappingCone.snd (mappingPostcompose A X f)).v q q (add_zero _) z) := by
  have h := congrArg (fun g => g z)
    (mappingCone.d_snd_v (mappingPostcompose A X f) q (q + 1) rfl)
  exact h

/--
概要：二つの cochain から作った cone cochain の微分の正規形。
方針：liftCochain の微分公式を、cone の二成分の順序へ整理する。
規約：第一成分は負の微分、第二成分は後合成と微分の和。
使われ方：Drinfeld §2.4、KST D4 の cone の chain 比較。
-/
lemma coneLift_differential {X Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) (q : ℤ)
    (a : Cochain X Y (q + 1)) (b : Cochain X Z q) :
    δ q (q + 1) (mappingCone.liftCochain f a b rfl) =
      mappingCone.liftCochain f (-δ (q + 1) (q + 1 + 1) a)
        (a.comp (Cochain.ofHom f) (add_zero _) + δ q (q + 1) b) rfl := by
  rw [mappingCone.δ_liftCochain f a b rfl (q + 1 + 1) rfl]
  simp only [mappingCone.liftCochain, Cochain.neg_comp]
  rw [add_comm (δ q (q + 1) b)]

/--
概要：写像複体の cone から、標的の cone の写像複体への比較射。
方針：二成分の線形写像と liftCochain の微分公式で chain 条件を示す。
規約：比較射の微分との可換性を実際に証明する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の cone の代表可能性。
-/
def mappingConeComparison (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    mappingCone (mappingPostcompose A X f) ⟶ mappingComplex A X (mappingCone f) :=
  CochainComplex.ofHom (mappingConeComponent A X f) (fun q => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change δ q (q + 1) (mappingCone.liftCochain f
      ((mappingCone.fst (mappingPostcompose A X f)).val.v q (q + 1) rfl z)
      ((mappingCone.snd (mappingPostcompose A X f)).v q q (add_zero q) z) rfl) =
      mappingCone.liftCochain f
        ((mappingCone.fst (mappingPostcompose A X f)).val.v (q + 1) (q + 1 + 1) rfl
          ((mappingCone (mappingPostcompose A X f)).d q (q + 1) z))
        ((mappingCone.snd (mappingPostcompose A X f)).v (q + 1) (q + 1) (add_zero _)
          ((mappingCone (mappingPostcompose A X f)).d q (q + 1) z)) rfl
    exact (coneLift_differential f q _ _).trans
      (congrArg₂ (fun a b => mappingCone.liftCochain f a b rfl)
        (mappingCone_fst_d A X f q z).symm (mappingCone_snd_d A X f q z).symm))

/--
概要：元の cone へ入る cochain の二成分から、写像複体の cone の元を復元する。
方針：元の cone の第一・第二射影で取り出し、加群複体の cone へ戻す。
規約：比較射の逆を次数ごとに具体的に指定する。
使われ方：Drinfeld §2.4、KST D4 の cone の代表可能性。
-/
def mappingConeInverseElement (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ}
    (f : Y ⟶ Z) (q : ℤ) (z : (mappingComplex A X (mappingCone f)).X q) :
    (mappingCone (mappingPostcompose A X f)).X q :=
  complexConeElementMk A (mappingPostcompose A X f) q
    (z.comp (mappingCone.fst f).val rfl)
    (z.comp (mappingCone.snd f) (add_zero q))

/--
概要：二成分から復元して比較射を適用すると元の cochain に戻る。
方針：元の cone の二つの射影で一致を判定する。
規約：任意の整数次数で証明する。
使われ方：Drinfeld §2.4、KST D4 の cone の chain 同型。
-/
theorem mappingConeComparison_rightInverse (X : CochainComplex C ℤ)
    {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) (q : ℤ) :
    Function.RightInverse (mappingConeInverseElement A X f q)
      ((mappingConeComparison A X f).f q) := by
  intro z
  apply (mappingCone.ext_cochain_to_iff f q (q + 1) rfl).mpr
  constructor
  · exact (mappingCone.liftCochain_fst f _ _ rfl).trans
      (complexConeElementMk_fst A (mappingPostcompose A X f) q _ _)
  · exact (mappingCone.liftCochain_snd f _ _ rfl).trans
      (complexConeElementMk_snd A (mappingPostcompose A X f) q _ _)

/--
概要：比較射の像を二成分で復元すると元の cone の元に戻る。
方針：加群複体の cone の元を二つの射影で判定する。
規約：次数ごとの逆の両側条件を明示する。
使われ方：Drinfeld §2.4、KST D4 の cone の chain 同型。
-/
theorem mappingConeComparison_leftInverse (X : CochainComplex C ℤ)
    {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) (q : ℤ) :
    Function.LeftInverse (mappingConeInverseElement A X f q)
      ((mappingConeComparison A X f).f q) := by
  intro z
  apply complexConeElement_ext A (mappingPostcompose A X f) q
  · exact (complexConeElementMk_fst A (mappingPostcompose A X f) q _ _).trans
      (mappingCone.liftCochain_fst f _ _ rfl)
  · exact (complexConeElementMk_snd A (mappingPostcompose A X f) q _ _).trans
      (mappingCone.liftCochain_snd f _ _ rfl)

/--
概要：写像複体の cone 比較射は同型。
方針：具体的な二成分の逆写像から各次数の全単射を証明する。
規約：微分との可換性は比較射の構成で証明済み。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
instance mappingConeComparison_isIso (X : CochainComplex C ℤ)
    {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) : IsIso (mappingConeComparison A X f) := by
  have (q : ℤ) : IsIso ((mappingConeComparison A X f).f q) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(mappingConeComparison_leftInverse A X f q).injective,
        (mappingConeComparison_rightInverse A X f q).surjective⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/--
概要：写像複体上の cone と元の cone への写像複体の具体的な chain 同型。
方針：二成分の比較射を同型として束ねる。
規約：有界性や平坦性を仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の cone の代表可能性。
-/
def mappingConeIso (X : CochainComplex C ℤ) {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    mappingCone (mappingPostcompose A X f) ≅ mappingComplex A X (mappingCone f) :=
  asIso (mappingConeComparison A X f)

/--
概要：cone へ入る cochain の二成分表示は任意次数の前合成と両立する。
方針：liftCochain の二つの合成へ結合則を適用する。
規約：次数零の前合成に限定しない。
使われ方：Drinfeld §2.4、KST D4 の cone 代表加群の全次数自然性。
-/
theorem comp_coneLift {T X Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) {p r n : ℤ}
    (a : Cochain T X p) (b : Cochain X Y (r + 1)) (c : Cochain X Z r) (h : p + r = n) :
    a.comp (mappingCone.liftCochain f b c rfl) h =
      mappingCone.liftCochain f (a.comp b (by omega)) (a.comp c h) rfl := by
  unfold mappingCone.liftCochain
  rw [Cochain.comp_add,
    ← Cochain.comp_assoc a b (mappingCone.inl f)
      (show p + (r + 1) = n + 1 by omega)
      (show (r + 1) + (-1) = r by omega)
      (show p + (r + 1) + (-1) = n by omega),
    ← Cochain.comp_assoc_of_third_is_zero_cochain]

/--
概要：cone へ入る cochain の二成分表示は符号倍と両立する。
方針：二つの成分の合成の加法線形性を使う。
規約：Koszul 符号の整数単元による作用を扱う。
使われ方：Drinfeld §2.4、KST D4 の cone の符号の照合。
-/
theorem coneLift_units_smul {X Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) (r : ℤ)
    (b : Cochain X Y (r + 1)) (c : Cochain X Z r) (k : ℤˣ) :
    mappingCone.liftCochain f (k • b) (k • c) rfl =
      k • mappingCone.liftCochain f b c rfl := by
  simp only [mappingCone.liftCochain, Cochain.units_smul_comp, smul_add]

end SerrePositivity.KST.DerivedGeometry.LinearComplex
