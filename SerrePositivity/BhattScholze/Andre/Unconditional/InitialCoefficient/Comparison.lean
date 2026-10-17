module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientIdealQuotient
public import SerrePositivity.BhattScholze.Andre.PowerRootMonicQuotient

/-!
# A1-d：無限根初期係数商と通常モニック商

## 概要
P/(p,dP,f(Y₀)) を A/(p,d) 上の通常モニック無限根商と比較する。
BS Rem 7.15（著者版 p.62）の raw 残余商へ渡す係数の忠実平坦性。

## 方針
係数商と無限根環の交換を用い、同じ f の関係を課してから係数作用を照合する。

## 規約
d は任意の係数元。hpR、係数商の非零性、追加の平坦性は仮定しない。

## 使われ方
完全 prism の d に適用して、元の raw 残余商への忠実平坦性と合成する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.InitialCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (d : A) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "y" => powerRootMonicPDInput p f
local notation "I" => Ideal.span {(p : A), d}
local notation "R" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "IP" => Ideal.map (algebraMap A P) I
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (algebraMap A P d) a
local notation "Q" => P ⧸ J
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "ybar" => powerRootPolynomialBaseMap R p hp (f.map q)
local notation "M" => PowerRootPolynomialQuotient R p hp (f.map q)

/-- 概要：初期係数イデアルは係数 (p,d) の拡張と f(Y₀) の関係の和。
方針：一元分子族の像と二元係数イデアルの像を展開する。
規約：モニック性や正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の同じ通常商の比較。 -/
theorem initialCoefficientIdeal_eq : J = IP ⊔ Ideal.span {y} := by
  rw [deltaDivisionFirstBaseIdeal, Ideal.map_span, Set.image_pair, map_natCast]
  congr 1
  apply congrArg Ideal.span
  ext z
  simp

/-- 概要：初期係数商は係数商上で f(Y₀) を零にする無限根環と環同型。
方針：係数商と関係商の順序を交換し、係数還元の入力評価公式を使う。
規約：通常の元の商を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の通常モニック商への係数比較。 -/
def initialCoefficientPrincipalEquiv : Q ≃+* Pbar ⧸ Ideal.span {ybar} := by
  let e := powerRootCoefficientIdealQuotientEquiv A p hp I
  have he : e (Ideal.Quotient.mk IP y) = ybar := by
    rw [powerRootCoefficientIdealQuotientEquiv_mk]
    unfold powerRootMonicPDInput
    exact powerRootCoefficientIdealQuotientMap_baseMap A p hp I f
  have hmap : (Ideal.span {y}).map (Ideal.Quotient.mk IP) =
      Ideal.span {Ideal.Quotient.mk IP y} := by
    simpa only [Set.image_singleton] using (Ideal.map_span (Ideal.Quotient.mk IP) {y})
  have heIdeal : (Ideal.span {Ideal.Quotient.mk IP y}).map e.toRingHom = Ideal.span {ybar} := by
    have hx : (Ideal.span {Ideal.Quotient.mk IP y}).map e.toRingHom =
        Ideal.span {e (Ideal.Quotient.mk IP y)} := by
      exact (Ideal.map_span e.toRingHom {Ideal.Quotient.mk IP y}).trans
        (congrArg Ideal.span (Set.image_singleton (f := e.toRingHom)))
    exact hx.trans (congrArg (fun t : Pbar => Ideal.span {t}) he)
  let eQ := Ideal.quotientEquiv _ _ e heIdeal.symm
  exact (Ideal.quotEquivOfEq (initialCoefficientIdeal_eq (p := p) d f)).trans
    ((DoubleQuot.quotQuotEquivQuotSup IP (Ideal.span {y})).symm.trans
      ((Ideal.quotEquivOfEq hmap).trans eQ))

/-- 概要：主関係商との比較は元の無限根環の全代表元を保つ。
方針：二重商と係数還元の代表元公式を合成する。
規約：係数・根変数に限定せず全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な係数射の同定。 -/
theorem initialCoefficientPrincipalEquiv_mk (x : P) :
    initialCoefficientPrincipalEquiv (p := p) d f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (powerRootCoefficientIdealQuotientMap A p hp I x) := by
  rfl

/-- 概要：初期係数商を既存の PowerRootPolynomialQuotient そのものへ同定する。
方針：f(Y₀) の主イデアルと通常多項式から拡張した関係イデアルの一致を使う。
規約：モニック性は同型の仮定にしない。
使われ方：BS Rem 7.15（著者版 p.62）の既存のモニック商基底 API への接続。 -/
def initialCoefficientEquiv : Q ≃+* M :=
  (initialCoefficientPrincipalEquiv (p := p) d f).trans
    (Ideal.quotEquivOfEq (powerRootPolynomialQuotient_ideal R p hp (f.map q)).symm)

/-- 概要：標準モニック商への同型は元の係数を同じ係数商の標準像へ送る。
方針：主関係商の代表元公式と無限根係数還元の公式を使う。
規約：全ての A 係数を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の A/(p,d) 作用の照合。 -/
theorem initialCoefficientEquiv_coeff (x : A) :
    initialCoefficientEquiv (p := p) d f (Ideal.Quotient.mk J (algebraMap A P x)) =
      algebraMap R M (q x) := by
  rw [initialCoefficientEquiv, RingEquiv.trans_apply, initialCoefficientPrincipalEquiv_mk,
    powerRootCoefficientIdealQuotientMap_coeff, Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：A/(p,d) から元の初期係数商への係数射。
方針：通常モニック商の係数射を比較同型で戻す。
規約：次の全係数公式で自然な作用を検証する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 残余商への係数射の合成。 -/
def initialCoefficientBaseMap : R →+* Q :=
  (initialCoefficientEquiv (p := p) d f).symm.toRingHom.comp (algebraMap R M)

/-- 概要：初期係数商の係数射は元の係数の標準商像で与えられる。
方針：係数を保つ比較同型の単射性を使う。
規約：元の A の任意元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な基底作用の保証。 -/
theorem initialCoefficientBaseMap_mk (x : A) :
    initialCoefficientBaseMap (p := p) d f (q x) = Ideal.Quotient.mk J (algebraMap A P x) := by
  apply (initialCoefficientEquiv (p := p) d f).injective
  change initialCoefficientEquiv (p := p) d f ((initialCoefficientEquiv (p := p) d f).symm _) = _
  rw [RingEquiv.apply_symm_apply, initialCoefficientEquiv_coeff]

/-- 概要：自然な係数射による初期係数商の代数構造。
方針：検証済みの係数環射から構成する。
規約：利用時に局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性の型。 -/
@[instance_reducible] def initialCoefficientAlgebra : Algebra R Q :=
  (initialCoefficientBaseMap (p := p) d f).toAlgebra

/-- 概要：通常モニック商との比較は A/(p,d) 代数同型。
方針：係数射の定義から可換性を確認する。
規約：単なる環同型でなく同じ係数作用を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の基底と忠実平坦性の移送。 -/
def initialCoefficientAlgEquiv :
    let := initialCoefficientAlgebra (p := p) d f
    Q ≃ₐ[R] M := by
  let := initialCoefficientAlgebra (p := p) d f
  exact { initialCoefficientEquiv (p := p) d f with
    commutes' := fun _ => (initialCoefficientEquiv (p := p) d f).apply_symm_apply _ }

/-- 概要：モニック初期係数商は A/(p,d) 上自由。
方針：既存の通常モニック無限根商の基底を係数代数同型で戻す。
規約：正次数・hpR は不要。
使われ方：BS Rem 7.15（著者版 p.62）の初期係数商の平坦性。 -/
theorem initialCoefficient_free (hf : f.Monic) :
    let := initialCoefficientAlgebra (p := p) d f
    Module.Free R Q := by
  let := initialCoefficientAlgebra (p := p) d f
  let := powerRootPolynomialQuotient_free R p hp (f.map q) (hf.map q)
  exact Module.Free.of_equiv (initialCoefficientAlgEquiv (p := p) d f).symm.toLinearEquiv

/-- 概要：正次数モニック初期係数商は A/(p,d) 上忠実平坦。
方針：零係数商を分け、非零枝では次数保存と既存のモニック商の忠実平坦性を使う。
規約：係数商の非零性を追加せず、hpR も不要。
使われ方：BS Rem 7.15（著者版 p.62）の raw 残余商への忠実平坦性の第一段。 -/
theorem initialCoefficient_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := initialCoefficientAlgebra (p := p) d f
    Module.FaithfullyFlat R Q := by
  let := initialCoefficientAlgebra (p := p) d f
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    let := initialCoefficient_free (p := p) d f hf
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    have hdeg' : 0 < (f.map q).natDegree := by simpa only [hf.natDegree_map] using hdeg
    let := powerRootPolynomialQuotient_faithfullyFlat R p hp (f.map q) (hf.map q) hdeg'
    exact Module.FaithfullyFlat.of_linearEquiv R M
      (initialCoefficientAlgEquiv (p := p) d f).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.InitialCoefficient
