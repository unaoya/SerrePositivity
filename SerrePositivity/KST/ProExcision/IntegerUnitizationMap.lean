module
public import SerrePositivity.KST.ProExcision.IntegerUnitization

/-!
# 非単位環準同型の整数単位化への拡張

概要：非可換な非単位環準同型を整数単位化の単位環準同型に拡張し、係数イデアルを保つことを証明する。
方針：整数線形な非単位代数準同型として既存の単位化の普遍写像へ渡す。
規約：KST Lemma 4.16 の非単位単体環の標準の理想模型。
使われ方：任意の非単位単体環の図式から SimplicialIdealData を構成する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {I : Type u} {J : Type v} {K : Type w} [NonUnitalRing I] [NonUnitalRing J] [NonUnitalRing K]

/-- 概要：非単位環準同型を整数の非単位代数準同型とする。
方針：加法群準同型の整数倍の保存を使う。
規約：KST 4.16、I,J は非可換でよい。
使われ方：整数単位化への拡張の入力。 -/
def integerNonUnitalAlgHom (f : I →ₙ+* J) : I →ₙₐ[ℤ] J where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add
  map_mul' := f.map_mul
  map_smul' z x := map_intCast_smul f ℤ ℤ z x

/-- 概要：非単位環準同型の整数単位化への標準の拡張。
方針：標的の単位化の包含へ合成し、単位化の普遍写像を使う。
規約：KST 4.16、整数成分を固定し第二成分に f を適用する。
使われ方：非単位単体環の面・退化の単位化。 -/
def integerUnitizationMap (f : I →ₙ+* J) : Unitization ℤ I →+* Unitization ℤ J :=
  ((Unitization.inrNonUnitalAlgHom ℤ J).comp (integerNonUnitalAlgHom f)).toAlgHom.toRingHom

/-- 概要：整数単位化への拡張は整数成分を保つ。
方針：普遍写像の第一成分を計算する。
規約：KST 4.16。使われ方：係数イデアルの保存。 -/
lemma integerUnitizationMap_fst (f : I →ₙ+* J) (x : Unitization ℤ I) :
    (integerUnitizationMap f x).fst = x.fst := by
  change (algebraMap ℤ (Unitization ℤ J) x.fst + (f x.snd : Unitization ℤ J)).fst = _
  have hi : algebraMap ℤ (Unitization ℤ J) x.fst = Unitization.inl x.fst :=
    congrArg (fun g : ℤ →+* Unitization ℤ J ↦ g x.fst)
      (Subsingleton.elim _ (Unitization.inlRingHom ℤ J))
  rw [hi]
  simp only [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]

/-- 概要：整数単位化への拡張の第二成分は f による第二成分の像。
方針：普遍写像の第二成分を計算する。
規約：KST 4.16。使われ方：恒等・合成と指定元の自然性。 -/
lemma integerUnitizationMap_snd (f : I →ₙ+* J) (x : Unitization ℤ I) :
    (integerUnitizationMap f x).snd = f x.snd := by
  change (algebraMap ℤ (Unitization ℤ J) x.fst + (f x.snd : Unitization ℤ J)).snd = _
  have hi : algebraMap ℤ (Unitization ℤ J) x.fst = Unitization.inl x.fst :=
    congrArg (fun g : ℤ →+* Unitization ℤ J ↦ g x.fst)
      (Subsingleton.elim _ (Unitization.inlRingHom ℤ J))
  rw [hi]
  simp only [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

/-- 概要：元の非単位環の包含は整数単位化の写像に自然。
方針：二つの成分で拡張の公式を使う。
規約：KST 4.16。使われ方：零次の指定元の移送。 -/
lemma integerUnitizationMap_inr (f : I →ₙ+* J) (x : I) :
    integerUnitizationMap f (x : Unitization ℤ I) = (f x : Unitization ℤ J) := by
  apply Unitization.ext
  · simp only [integerUnitizationMap_fst, Unitization.fst_inr]
  · simp only [integerUnitizationMap_snd, Unitization.snd_inr]

/-- 概要：整数単位化の写像は恒等準同型を保つ。
方針：第一・第二成分の外延性を使う。
規約：KST 4.16。使われ方：単体的単位化の恒等法則。 -/
lemma integerUnitizationMap_id : integerUnitizationMap (NonUnitalRingHom.id I) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Unitization.ext
  · exact integerUnitizationMap_fst _ x
  · exact integerUnitizationMap_snd _ x

/-- 概要：整数単位化の写像は準同型の合成を保つ。
方針：二成分で写像の合成を計算する。
規約：KST 4.16。使われ方：単体的単位化の合成法則。 -/
lemma integerUnitizationMap_comp (f : I →ₙ+* J) (g : J →ₙ+* K) :
    integerUnitizationMap (g.comp f) = (integerUnitizationMap g).comp (integerUnitizationMap f) := by
  apply RingHom.ext
  intro x
  apply Unitization.ext
  · simp only [RingHom.comp_apply, integerUnitizationMap_fst]
  · simp only [RingHom.comp_apply, integerUnitizationMap_snd, NonUnitalRingHom.comp_apply]

/-- 概要：整数単位化の写像は元の非単位環の係数イデアルを保つ。
方針：核の条件は整数成分が零であることを使う。
規約：KST 4.16 の I の標準の理想模型。
使われ方：単体的イデアルの図式を作る。 -/
lemma integerUnitizationMap_ideal (f : I →ₙ+* J) (x : Unitization ℤ I)
    (hx : x ∈ integerUnitizationIdeal I) : integerUnitizationMap f x ∈ integerUnitizationIdeal J := by
  rw [mem_integerUnitizationIdeal] at hx ⊢
  rw [integerUnitizationMap_fst]
  exact hx

end SerrePositivity.KST.ProExcision
