module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion

/-!
# prism 係数の商に沿う導来底変換

## 概要
A → A/(a) → A/(a,d)、冪剰余 A/(a,dⁿ) → A/(a,d)、mod p 還元に沿う導来底変換の比較と忠実平坦性の判定。
BS 著者版 Proposition 3.13 の底変換の計算に使う、prism 係数の商に沿う導来還元を扱う。

## 方針
既存の導来基底変更関手を標準的な因数分解に沿って比較する。

## 規約
原典に項目のない道具。

## 使われ方
André の一段の拡大と RootEnvelope の平坦性計算。
-/

universe u

/-! ## prism係数の二段商と実導来基底変更（旧 Prism/Residue/PrismaticCoefficientQuotientComposition.lean）

既存の実導来関手を、A→A/(a)→A/(a,d)の標準因数分解に沿って比較する。
-/

@[expose] public noncomputable section PrismaticCoefficientQuotientComposition

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A)
local notation "I₀" => Ideal.span (Set.singleton a)
local notation "J₀" => Ideal.span (Set.insert a (Set.singleton d))
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "r₀" => Ideal.Quotient.mk J₀

/-- prism係数の二段商における標準の第2商射。 -/
def prismaticCoefficientPrincipalQuotientMap : A ⧸ I₀ →+* A ⧸ J₀ :=
  Ideal.quotientMap J₀ (RingHom.id A) (by
    intro x hx
    change x ∈ J₀
    exact (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) hx)

local notation "s₀" => prismaticCoefficientPrincipalQuotientMap a d

/-- 二段商の合成は、実際の(a,d)商射そのもの。 -/
theorem prismaticCoefficientPrincipalQuotientMap_comp : (s₀).comp q₀ = r₀ := by
  apply RingHom.ext
  intro x
  rfl

/-- 通常係数拡大の二段商比較はMathlibの標準合成比較から得る。 -/
def prismaticCoefficientScalarExtensionCompositionIso :
    ModuleCat.extendScalars r₀ ≅ ModuleCat.extendScalars q₀ ⋙ ModuleCat.extendScalars s₀ :=
  eqToIso (congrArg ModuleCat.extendScalars
      (prismaticCoefficientPrincipalQuotientMap_comp a d).symm) ≪≫
    ModuleCat.extendScalarsComp q₀ s₀

/-- 二段商の比較は複体上でも自然に成立する。 -/
def prismaticCoefficientCochainCompositionIso :
    (ModuleCat.extendScalars r₀).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars s₀).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (prismaticCoefficientScalarExtensionCompositionIso a d).symm (.up ℤ)).symm

/-- 実(a,d)基底変更は、標準二段商に沿う二つの実導来基底変更と同型。 -/
def prismaticCoefficientDerivedQuotientCompositionIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).obj X ≅
      (boundedAboveDerivedBaseChange s₀).obj ((boundedAboveDerivedBaseChange q₀).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticCoefficientCochainCompositionIso a d).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedBaseChangeModelIso s₀ ((boundedAboveDerivedBaseChange q₀).obj X)
        (boundedAboveDerivedBaseChangeModel q₀ X)).symm)

/-- 二段商の実導来比較は、全ての実導来射に自然。 -/
theorem prismaticCoefficientDerivedQuotientCompositionIso_naturality
    {X Y : DerivedCategory.Minus (ModuleCat.{u} A)} (f : X ⟶ Y) :
    (boundedAboveDerivedBaseChange r₀).map f ≫
        (prismaticCoefficientDerivedQuotientCompositionIso a d Y).hom =
      (prismaticCoefficientDerivedQuotientCompositionIso a d X).hom ≫
        (boundedAboveDerivedBaseChange s₀).map ((boundedAboveDerivedBaseChange q₀).map f) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let S := boundedAboveDerivedBaseChangeModel q₀ X
  let T := boundedAboveDerivedBaseChangeModel q₀ Y
  let k := ((ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ)).map h
  have hk : DerivedCategory.Q.map k ≫ T.iso.hom =
      S.iso.hom ≫ ((boundedAboveDerivedBaseChange q₀).map f).hom := by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  have hr := boundedAboveLeftDerivedModelIso_naturality (ModuleCat.extendScalars s₀)
    S T ((boundedAboveDerivedBaseChange q₀).map f) k hk
  have hc := congrArg (fun g => DerivedCategory.Q.map g)
    ((prismaticCoefficientCochainCompositionIso a d).hom.naturality h)
  simp only [CategoryTheory.Functor.map_comp] at hc
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveDerivedBaseChangeModelIso s₀
    ((boundedAboveDerivedBaseChange q₀).obj Y) T).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    prismaticCoefficientDerivedQuotientCompositionIso, ObjectProperty.isoMk,
    ObjectProperty.homMk_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id]
  change DerivedCategory.Q.map
      (((ModuleCat.extendScalars r₀).mapHomologicalComplex (.up ℤ)).map h) ≫
        DerivedCategory.Q.map ((prismaticCoefficientCochainCompositionIso a d).hom.app Q.complex) =
    DerivedCategory.Q.map ((prismaticCoefficientCochainCompositionIso a d).hom.app P.complex) ≫
      (boundedAboveLeftDerivedModelIso (ModuleCat.extendScalars s₀) _ S).inv ≫
        ((boundedAboveLeftDerived (ModuleCat.extendScalars s₀)).map
          ((boundedAboveDerivedBaseChange q₀).map f)).hom ≫
        (boundedAboveLeftDerivedModelIso (ModuleCat.extendScalars s₀) _ T).hom
  rw [hr, Iso.inv_hom_id_assoc]
  exact hc

/-- 二段商比較の、実導来関手の自然同型としての公開入口。 -/
def prismaticCoefficientDerivedQuotientCompositionNatIso :
    boundedAboveDerivedBaseChange r₀ ≅
      boundedAboveDerivedBaseChange q₀ ⋙ boundedAboveDerivedBaseChange s₀ :=
  NatIso.ofComponents (prismaticCoefficientDerivedQuotientCompositionIso a d)
    (fun f => prismaticCoefficientDerivedQuotientCompositionIso_naturality a d f)

end SerrePositivity.BhattScholze

end PrismaticCoefficientQuotientComposition

/-! ## 正則主元の完備化単位の二生成係数商還元（旧 Prism/Residue/PrismaticCoefficientCompletionReduction.lean）

a,dを個別に正則とする場合にも、d mod aの正則性は仮定しない。
-/

@[expose] public noncomputable section PrismaticCoefficientCompletionReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A)
local notation "q₀" => Ideal.Quotient.mk (Ideal.span (Set.singleton a))
local notation "r₀" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton d)))
local notation "s₀" => prismaticCoefficientPrincipalQuotientMap a d
local notation "C₀" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A a
local notation "U₀" => DerivedCompletion.boundedAboveDerivedCompletionUnit A a

/-- 正則aの標準完備化単位は、実(a,d)還元後にも同型となる。 -/
theorem prismaticCoefficientCompletion_pair_unit_isIso (ha : IsSMulRegular A a)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    IsIso ((boundedAboveDerivedBaseChange r₀).map ((U₀).app X)) := by
  have hq : IsIso ((boundedAboveDerivedBaseChange q₀).map ((U₀).app X)) := by
    let F (J : Ideal A) := IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).map
      ((U₀).app X))
    have h : F (Ideal.span {a ^ 1}) :=
      DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A a ha 1 X
    have hJ : Ideal.span {a ^ 1} = Ideal.span {a} := by rw [pow_one]
    exact Eq.mp (congrArg F hJ) h
  have := hq
  let e := prismaticCoefficientDerivedQuotientCompositionNatIso a d
  have hn := e.hom.naturality ((U₀).app X)
  have hi : IsIso ((boundedAboveDerivedBaseChange r₀).map ((U₀).app X) ≫
      e.hom.app ((C₀).obj X)) := by
    rw [hn]
    change IsIso (e.hom.app X ≫ (boundedAboveDerivedBaseChange s₀).map
      ((boundedAboveDerivedBaseChange q₀).map ((U₀).app X)))
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app ((C₀).obj X))

/-- 実(a,d)還元の完備化比較は、標準完備化単位の像そのもの。 -/
def prismaticCoefficientCompletionPairIso (ha : IsSMulRegular A a)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).obj X ≅
      (boundedAboveDerivedBaseChange r₀).obj ((C₀).obj X) := by
  have := prismaticCoefficientCompletion_pair_unit_isIso a d ha X
  exact asIso ((boundedAboveDerivedBaseChange r₀).map ((U₀).app X))

/-- 完備化比較の逆射は、実還元した標準単位の左逆。 -/
theorem prismaticCoefficientCompletionPairIso_unit (ha : IsSMulRegular A a)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).map ((U₀).app X) ≫
      (prismaticCoefficientCompletionPairIso a d ha X).inv = 𝟙 _ :=
  (prismaticCoefficientCompletionPairIso a d ha X).hom_inv_id

/-- 標準単位の像による比較は、既存実関手の自然同型を与える。 -/
def prismaticCoefficientCompletionPairNatIso (ha : IsSMulRegular A a) :
    boundedAboveDerivedBaseChange r₀ ≅ C₀ ⋙ boundedAboveDerivedBaseChange r₀ := by
  refine NatIso.ofComponents (prismaticCoefficientCompletionPairIso a d ha) ?_
  intro X Y f
  change (boundedAboveDerivedBaseChange r₀).map f ≫
      (boundedAboveDerivedBaseChange r₀).map ((U₀).app Y) =
    (boundedAboveDerivedBaseChange r₀).map ((U₀).app X) ≫
      (boundedAboveDerivedBaseChange r₀).map ((C₀).map f)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (boundedAboveDerivedBaseChange r₀).map ((U₀).naturality f)

/-- 正則dの標準d完備化単位も、同じ実(a,d)還元で同型となる。 -/
theorem prismaticCoefficientCompletion_second_pair_unit_isIso (hd : IsSMulRegular A d)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    IsIso ((boundedAboveDerivedBaseChange r₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A d).app X)) := by
  let F (J : Ideal A) := IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).map
    ((DerivedCompletion.boundedAboveDerivedCompletionUnit A d).app X))
  have h : F (Ideal.span {d, a}) := prismaticCoefficientCompletion_pair_unit_isIso d a hd X
  have hJ : Ideal.span {d, a} = Ideal.span {a, d} := by rw [Set.pair_comm]
  exact Eq.mp (congrArg F hJ) h

/-- 二つの正則主元の既存実完備化を逐次施しても、実(a,d)還元は元と同型。 -/
def prismaticCoefficientIteratedCompletionPairIso (ha : IsSMulRegular A a)
    (hd : IsSMulRegular A d) (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A d).obj ((C₀).obj X)) ≅
      (boundedAboveDerivedBaseChange r₀).obj X := by
  have hi := prismaticCoefficientCompletion_second_pair_unit_isIso a d hd ((C₀).obj X)
  exact (asIso ((boundedAboveDerivedBaseChange r₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A d).app ((C₀).obj X)))).symm ≪≫
    (prismaticCoefficientCompletionPairIso a d ha X).symm

/-- 逐次比較は、二つの標準単位の合成を実還元した射の左逆となる。 -/
theorem prismaticCoefficientIteratedCompletionPairIso_unit (ha : IsSMulRegular A a)
    (hd : IsSMulRegular A d) (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).map (((U₀).app X) ≫
        (DerivedCompletion.boundedAboveDerivedCompletionUnit A d).app ((C₀).obj X)) ≫
      (prismaticCoefficientIteratedCompletionPairIso a d ha hd X).hom = 𝟙 _ := by
  have := prismaticCoefficientCompletion_second_pair_unit_isIso a d hd ((C₀).obj X)
  simp only [prismaticCoefficientIteratedCompletionPairIso, Functor.map_comp,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [IsIso.hom_inv_id_assoc]
  exact prismaticCoefficientCompletionPairIso_unit a d ha X

end SerrePositivity.BhattScholze

end PrismaticCoefficientCompletionReduction

/-! ## prism係数の冪剰余と冪零厚化（旧 Prism/Residue/PrismaticPowerResidueNilpotent.lean）

A/(a,dⁿ)からA/(a,d)への具体的な冪零商。n>0の標準射を固定する。
-/

@[expose] public noncomputable section PrismaticPowerResidueNilpotent

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ)
local notation "Jₙ" => Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "J₁" => Ideal.span (Set.insert a (Set.singleton d))
local notation "Tₙ" => A ⧸ Jₙ
local notation "qₙ" => Ideal.Quotient.mk Jₙ
local notation "q₁" => Ideal.Quotient.mk J₁

/-- 冪剰余A/(a,dⁿ)の中でdの像が生成するイデアル。 -/
def prismaticPowerResidueIdeal : Ideal Tₙ := Ideal.span {qₙ d}

/-- dの像の主イデアルはn乗で零。n=0の零環も含む。 -/
theorem prismaticPowerResidueIdeal_pow :
    prismaticPowerResidueIdeal a d n ^ n = ⊥ := by
  have hd : qₙ d ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [prismaticPowerResidueIdeal, Ideal.span_singleton_pow, hd]
  simp

/-- 正の冪について、二生成イデアル(a,dⁿ)は(a,d)に含まれる。 -/
theorem prismaticPowerResidue_sourceIdeal_le (hn : 0 < n) : Jₙ ≤ J₁ := by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.pow_mem_of_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) n hn

/-- 正の冪剰余から一乗剰余への標準環射。 -/
def prismaticPowerResidueMap (hn : 0 < n) : Tₙ →+* A ⧸ J₁ :=
  Ideal.quotientMap J₁ (RingHom.id A) (by
    intro x hx
    exact prismaticPowerResidue_sourceIdeal_le a d n hn hx)

/-- 標準射の合成は元のAからの(a,d)商射そのもの。 -/
theorem prismaticPowerResidueMap_comp (hn : 0 < n) :
    (prismaticPowerResidueMap a d n hn).comp qₙ = q₁ := rfl

/-- 冪剰余から一乗剰余への標準射は全射。 -/
theorem prismaticPowerResidueMap_surjective (hn : 0 < n) :
    Function.Surjective (prismaticPowerResidueMap a d n hn) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- (a,d)の冪剰余への像はdの像の主イデアルである。 -/
theorem prismaticPowerResidueIdeal_eq_map :
    (J₁).map qₙ = prismaticPowerResidueIdeal a d n := by
  have ha : qₙ a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change qₙ a ∈ prismaticPowerResidueIdeal a d n
      rw [ha]
      exact Ideal.zero_mem _
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact Ideal.subset_span (Set.mem_singleton _)
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mem_map_of_mem qₙ
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- 標準全射の核は具体的な冪零イデアルKₙである。 -/
theorem prismaticPowerResidueMap_ker (hn : 0 < n) :
    RingHom.ker (prismaticPowerResidueMap a d n hn) =
      prismaticPowerResidueIdeal a d n := by
  rw [prismaticPowerResidueMap, Ideal.quotientMap, Ideal.ker_quotient_lift]
  simpa only [RingHom.comp_id, Ideal.mk_ker] using prismaticPowerResidueIdeal_eq_map a d n

/-- Kₙでさらに商を取ると、標準写像に沿ってA/(a,d)を得る。 -/
def prismaticPowerResidueQuotientEquiv (hn : 0 < n) :
    Tₙ ⧸ prismaticPowerResidueIdeal a d n ≃+* A ⧸ J₁ :=
  (Ideal.quotEquivOfEq (prismaticPowerResidueMap_ker a d n hn).symm).trans
    (RingHom.quotientKerEquivOfSurjective (prismaticPowerResidueMap_surjective a d n hn))

/-- 冪零商の同型は、具体的な標準全射を保つ。 -/
theorem prismaticPowerResidueQuotientEquiv_comp_mk (hn : 0 < n) :
    (prismaticPowerResidueQuotientEquiv a d n hn).toRingHom.comp
        (Ideal.Quotient.mk (prismaticPowerResidueIdeal a d n)) =
      prismaticPowerResidueMap a d n hn := by
  apply RingHom.ext
  intro x
  rfl

end SerrePositivity.BhattScholze

end PrismaticPowerResidueNilpotent

/-! ## 冪零prism剰余を経由する実導来基底変更（旧 Prism/Residue/PrismaticPowerResidueDerived.lean）

A→A/(a,dⁿ)→A/(a,d)の標準射に沿って、二つの実導来対象を比較する。
-/

@[expose] public noncomputable section PrismaticPowerResidueDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
local notation "qₙ" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton (d ^ n))))
local notation "q₁" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton d)))
local notation "rₙ" => prismaticPowerResidueMap a d n hn

/-- 冪零剰余射を経由する通常基底変更の複体上での標準合成比較。 -/
def prismaticPowerResidueCochainCompositionIso :
    (ModuleCat.extendScalars q₁).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars qₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars rₙ).mapHomologicalComplex (.up ℤ) := by
  let e : ModuleCat.extendScalars q₁ ≅
      ModuleCat.extendScalars qₙ ⋙ ModuleCat.extendScalars rₙ :=
    eqToIso (congrArg ModuleCat.extendScalars
        (prismaticPowerResidueMap_comp a d n hn).symm) ≪≫
      ModuleCat.extendScalarsComp qₙ rₙ
  exact (Functor.mapHomologicalComplexCompIso e.symm (.up ℤ)).symm

/-- 実一乗剰余への基底変更を、実冪剰余と実冪零剰余射の二段階で計算する。 -/
def prismaticPowerResidueDerivedCompositionIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange q₁).obj X ≅
      (boundedAboveDerivedBaseChange rₙ).obj
        ((boundedAboveDerivedBaseChange qₙ).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticPowerResidueCochainCompositionIso a d n hn).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedBaseChangeModelIso rₙ ((boundedAboveDerivedBaseChange qₙ).obj X)
        (boundedAboveDerivedBaseChangeModel qₙ X)).symm)

end SerrePositivity.BhattScholze

end PrismaticPowerResidueDerived

/-! ## G10の標準冪零商射に沿う実還元との比較（旧 Prism/Residue/PrismaticPowerResidueCanonical.lean） -/

@[expose] public noncomputable section PrismaticPowerResidueCanonical

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal a d n
local notation "qₖ" => Ideal.Quotient.mk Kₙ
local notation "rₙ" => prismaticPowerResidueMap a d n hn
local notation "eₙ" => prismaticPowerResidueQuotientEquiv a d n hn

/-- 冪零商の逆同型は標準剰余射を標準商射へ戻す。 -/
theorem prismaticPowerResidueQuotientEquiv_symm_comp :
    (eₙ).symm.toRingHom.comp rₙ = qₖ := by
  apply RingHom.ext
  intro x
  apply (eₙ).injective
  change (eₙ) ((eₙ).symm ((rₙ) x)) = (eₙ) ((qₖ) x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (prismaticPowerResidueQuotientEquiv_comp_mk a d n hn) x).symm

/-- 標準冪零商への係数拡大は、既存剰余射と商同型による係数制限で計算できる。 -/
def prismaticPowerResidueCanonicalScalarIso :
    ModuleCat.extendScalars qₖ ≅
      ModuleCat.extendScalars rₙ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom :=
  eqToIso (congrArg ModuleCat.extendScalars
      (prismaticPowerResidueQuotientEquiv_symm_comp a d n hn).symm) ≪≫
    ModuleCat.extendScalarsComp rₙ (eₙ).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars rₙ)
        (restrictScalarsIsoExtendInverse eₙ).symm

/-- 同じ係数比較は複体上でも自然に成立する。 -/
def prismaticPowerResidueCanonicalCochainIso :
    (ModuleCat.extendScalars qₖ).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars rₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (eₙ).toRingHom).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (prismaticPowerResidueCanonicalScalarIso a d n hn).symm (.up ℤ)).symm

/-- G10の実標準商還元を、既証の実剰余還元の商同型による係数制限へ比較する。 -/
def prismaticPowerResidueCanonicalDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} Tₙ)) :
    (boundedAboveDerivedBaseChange qₖ).obj X ≅
      (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj
        ((boundedAboveDerivedBaseChange rₙ).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticPowerResidueCanonicalCochainIso a d n hn).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (eₙ).toRingHom).app
        (baseChange rₙ (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (eₙ).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso rₙ X (boundedAboveDerivedChosenModel X)).symm)

end SerrePositivity.BhattScholze

end PrismaticPowerResidueCanonical

/-! ## 実prism冪剰余へのG10と忠実性判定の適用（旧 Prism/Residue/PrismaticPowerDerivedFlat.lean） -/

@[expose] public noncomputable section PrismaticPowerDerivedFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span (Set.insert a (Set.singleton d))
local notation "Qₙ" => A ⧸ Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "q₀" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton d)))
local notation "qₙ" => Ideal.Quotient.mk (Ideal.span (Set.insert a (Set.singleton (d ^ n))))
local notation "Kₙ" => prismaticPowerResidueIdeal a d n
local notation "Sₙ" => Qₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv a d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X
local notation "Yₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Yₙ

/-- 実冪剰余の標準冪零還元を、元の実一乗剰余への係数制限へ比較する。 -/
def prismaticPowerCanonicalReductionIso :
    Wₙ ≅ (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj Y₀ :=
  prismaticPowerResidueCanonicalDerivedIso a d n hn Yₙ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      (prismaticPowerResidueDerivedCompositionIso a d n hn X).symm

include hn in
/-- 元の実(a,d)還元が次数零・忠実平坦なら、実(a,dⁿ)還元もそうである。 -/
theorem prismaticPowerDerivedReduction_pure_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  let H₀ := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj
  let Hₙ := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj
  let eH (i : ℤ) : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (Wₙ).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
        (DerivedCategory.Minus.ι.mapIso (prismaticPowerCanonicalReductionIso a d n hn X)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom i).app (Y₀).obj
  have hWzero (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (Wₙ).obj) :=
    ((ModuleCat.restrictScalars (eₙ).toRingHom).map_isZero (hzero i hi)).of_iso (eH i)
  have hWFF : Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (Wₙ).obj) := by
    let := (eₙ).toRingHom.toAlgebra
    let : Module Sₙ H₀ := Module.compHom H₀ (eₙ).toRingHom
    let : IsScalarTower Sₙ Q₀ H₀ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let eA : Sₙ ≃ₐ[Sₙ] Q₀ := AlgEquiv.ofBijective (Algebra.ofId Sₙ Q₀) (eₙ).bijective
    have : Module.FaithfullyFlat Sₙ Q₀ :=
      Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
    have : Module.FaithfullyFlat Q₀ H₀ := hFF
    have : Module.FaithfullyFlat Sₙ H₀ := Module.FaithfullyFlat.trans Sₙ Q₀ H₀
    exact Module.FaithfullyFlat.of_linearEquiv Sₙ H₀ (eH 0).toLinearEquiv
  let := hWFF
  obtain ⟨hGE, hLE, hFlat⟩ := derived_pure_flat_of_nilpotent_reduction Kₙ Yₙ hWzero
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow a d n⟩
  let := hGE
  let := hLE
  let eY : Yₙ ≅ boundedAboveDerivedSingleFunctor.obj Hₙ :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso (Yₙ).obj 0)
  let eRed : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (Wₙ).obj ≅
      (ModuleCat.extendScalars (Ideal.Quotient.mk Kₙ)).obj Hₙ :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)).mapIso eY)) ≪≫
      (boundedAboveDerivedBaseChangeModuleH0Iso (Ideal.Quotient.mk Kₙ)).app Hₙ
  have hTensor : Module.FaithfullyFlat Sₙ (Sₙ ⊗[Qₙ] Hₙ) := by
    let eQ := (quotientScalarExtensionEquiv Kₙ Hₙ).trans
      (quotientTensorReductionEquiv Kₙ Hₙ).symm
    exact Module.FaithfullyFlat.of_linearEquiv Sₙ _ (eRed.toLinearEquiv.trans eQ).symm
  refine ⟨hGE, hLE, ?_⟩
  dsimp only [prismaticPowerResidueIdeal] at hTensor
  let := hTensor
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Qₙ Hₙ).mpr
  refine ⟨hFlat, ?_⟩
  intro N _ _ hT
  apply subsingleton_of_power_torsion_of_residueTensor (qₙ d) Hₙ n N ?_ hT
  intro x
  have hz : (qₙ d) ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [hz, zero_smul]

end SerrePositivity.BhattScholze

end PrismaticPowerDerivedFlat

/-! ## 生成元冪商の標準mod p還元と二生成剰余（旧 Prism/Residue/PrismaticGeneratorPowerModP.lean）

G9のA/(dⁿ)上の標準mod p商と、G10側のA/(p,dⁿ)を比較する。
-/

@[expose] public noncomputable section PrismaticGeneratorPowerModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (p : ℕ) (d : A) (n : ℕ)
local notation "Iₙ" => Ideal.span (Set.singleton (d ^ n))
local notation "Jₙ" => Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Tₙ" => A ⧸ Iₙ
local notation "Qₙ" => A ⧸ Jₙ
local notation "qₙ" => Ideal.Quotient.mk Iₙ
local notation "qₚ" => Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ)))
local notation "q₀" => Ideal.Quotient.mk Jₙ

/-- 生成元冪商から二生成剰余への具体的標準射。 -/
def prismaticGeneratorPowerModPMap : Tₙ →+* Qₙ :=
  Ideal.quotientMap Jₙ (RingHom.id A) (by
    intro x hx
    change x ∈ Jₙ
    exact (Ideal.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hx)

local notation "rₙ" => prismaticGeneratorPowerModPMap p d n

/-- 元のAからの標準射との可換性。 -/
theorem prismaticGeneratorPowerModPMap_comp : (rₙ).comp qₙ = q₀ := rfl

/-- 生成元冪商から二生成剰余への標準射は全射。 -/
theorem prismaticGeneratorPowerModPMap_surjective : Function.Surjective rₙ :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- 標準射の核は、生成元冪商内のpの主イデアル。 -/
theorem prismaticGeneratorPowerModPMap_ker :
    RingHom.ker rₙ = Ideal.span {(p : Tₙ)} := by
  rw [prismaticGeneratorPowerModPMap, Ideal.quotientMap, Ideal.ker_quotient_lift]
  simp only [RingHom.comp_id, Ideal.mk_ker]
  have hd : qₙ (d ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self _)
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change qₙ (p : A) ∈ Ideal.span {(p : Tₙ)}
      rw [map_natCast]
      exact Ideal.mem_span_singleton_self _
    · obtain rfl := Set.mem_singleton_iff.mp hx
      change qₙ (d ^ n) ∈ Ideal.span {(p : Tₙ)}
      rw [hd]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [← map_natCast qₙ p]
    exact Ideal.mem_map_of_mem qₙ (Ideal.subset_span (Set.mem_insert _ _))

/-- 標準mod p商は二生成剰余Qₙに同型。n=0も含む。 -/
def prismaticGeneratorPowerModPEquiv : Tₙ ⧸ Ideal.span {(p : Tₙ)} ≃+* Qₙ :=
  (Ideal.quotEquivOfEq (prismaticGeneratorPowerModPMap_ker p d n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (prismaticGeneratorPowerModPMap_surjective p d n))

local notation "eₙ" => prismaticGeneratorPowerModPEquiv p d n

/-- mod p商同型は具体的な標準剰余射を保つ。 -/
theorem prismaticGeneratorPowerModPEquiv_comp_mk : (eₙ).toRingHom.comp qₚ = rₙ := by
  apply RingHom.ext
  intro x
  rfl

/-- 商同型の逆は、標準剰余射をG9の標準mod p商射へ戻す。 -/
theorem prismaticGeneratorPowerModPEquiv_symm_comp :
    (eₙ).symm.toRingHom.comp rₙ = qₚ := by
  apply RingHom.ext
  intro x
  apply (eₙ).injective
  change (eₙ) ((eₙ).symm ((rₙ) x)) = (eₙ) ((qₚ) x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (prismaticGeneratorPowerModPEquiv_comp_mk p d n) x).symm

/-- 二段階mod p還元と二生成剰余を比較する複体上の同型。 -/
def prismaticGeneratorPowerModPCochainIso :
    (ModuleCat.extendScalars qₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars qₚ).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (eₙ).toRingHom).mapHomologicalComplex (.up ℤ) := by
  have h : (qₚ).comp qₙ = (eₙ).symm.toRingHom.comp q₀ := by
    rw [← prismaticGeneratorPowerModPEquiv_symm_comp p d n,
      RingHom.comp_assoc, prismaticGeneratorPowerModPMap_comp]
  let e : ModuleCat.extendScalars qₙ ⋙ ModuleCat.extendScalars qₚ ≅
      ModuleCat.extendScalars q₀ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom :=
    (ModuleCat.extendScalarsComp qₙ qₚ).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars h) ≪≫
      ModuleCat.extendScalarsComp q₀ (eₙ).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars q₀)
        (restrictScalarsIsoExtendInverse eₙ).symm
  exact Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars q₀ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom))
      (.up ℤ)).symm

/-- G9の実標準mod p還元は、実Qₙ還元の商同型による係数制限と同型。 -/
def prismaticGeneratorPowerModPDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange qₚ).obj ((boundedAboveDerivedBaseChange qₙ).obj X) ≅
      (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedBaseChangeModelIso qₚ ((boundedAboveDerivedBaseChange qₙ).obj X)
        (boundedAboveDerivedBaseChangeModel qₙ X) ≪≫
      DerivedCategory.Q.mapIso ((prismaticGeneratorPowerModPCochainIso p d n).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (eₙ).toRingHom).app
        (baseChange q₀ (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (eₙ).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso q₀ X (boundedAboveDerivedChosenModel X)).symm)

variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₚ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X)
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X

/-- 標準mod p実還元のホモロジーと、実二生成剰余の係数制限との同型。 -/
def prismaticGeneratorPowerModPHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Z₀).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (prismaticGeneratorPowerModPDerivedIso p d n X)) ≪≫
    (derivedRestrictScalarsHomologyIso (eₙ).toRingHom i).app (Z₀).obj

/-- 実二生成剰余の次数消滅は、G9の標準mod p実還元へ移る。 -/
theorem prismaticGeneratorPowerModP_homology_isZero (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Z₀).obj)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Y₀).obj) :=
  ((ModuleCat.restrictScalars (eₙ).toRingHom).map_isZero h).of_iso
    (prismaticGeneratorPowerModPHomologyIso p d n X i)

/-- 実二生成剰余のH0平坦性は、正確なmod p商環上のH0平坦性へ移る。 -/
theorem prismaticGeneratorPowerModPH0_flat
    (h : Module.Flat Qₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj)) :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Y₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Mₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Mₙ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Mₙ ≃ₐ[Mₙ] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Mₙ Qₙ) (eₙ).bijective
  have : Module.Flat Mₙ Qₙ := Module.Flat.of_linearEquiv eA.symm.toLinearEquiv
  have : Module.Flat Qₙ M := h
  have : Module.Flat Mₙ M := Module.Flat.trans Mₙ Qₙ M
  exact Module.Flat.of_linearEquiv (R := Mₙ) (M := M)
    (prismaticGeneratorPowerModPHomologyIso p d n X 0).toLinearEquiv

end SerrePositivity.BhattScholze

end PrismaticGeneratorPowerModP

/-! ## 生成元冪商の標準mod p還元と二生成剰余（旧 Prism/Residue/PrismaticGeneratorPowerModPFaithful.lean）

G9のA/(dⁿ)上の標準mod p商と、G10側のA/(p,dⁿ)を比較する。
-/

@[expose] public noncomputable section PrismaticGeneratorPowerModPFaithful

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (p : ℕ) (d : A) (n : ℕ)
local notation "Iₙ" => Ideal.span (Set.singleton (d ^ n))
local notation "Jₙ" => Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Tₙ" => A ⧸ Iₙ
local notation "Qₙ" => A ⧸ Jₙ
local notation "qₙ" => Ideal.Quotient.mk Iₙ
local notation "qₚ" => Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ)))
local notation "q₀" => Ideal.Quotient.mk Jₙ

local notation "eₙ" => prismaticGeneratorPowerModPEquiv p d n

variable (X : DerivedCategory.Minus (ModuleCat.{u} A))

local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₚ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X)
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X

/-- 実二生成剰余のH0忠実平坦性は、正確なmod p商環上のH0忠実平坦性へ移る。 -/
theorem prismaticGeneratorPowerModPH0_faithfullyFlat
    (h : Module.FaithfullyFlat Qₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj)) :
    Module.FaithfullyFlat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Y₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Mₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Mₙ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Mₙ ≃ₐ[Mₙ] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Mₙ Qₙ) (eₙ).bijective
  have : Module.FaithfullyFlat Mₙ Qₙ :=
    Module.FaithfullyFlat.of_linearEquiv Mₙ Mₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Qₙ M := h
  have : Module.FaithfullyFlat Mₙ M := Module.FaithfullyFlat.trans Mₙ Qₙ M
  exact Module.FaithfullyFlat.of_linearEquiv (R := Mₙ) (M := M)
    (prismaticGeneratorPowerModPHomologyIso p d n X 0).toLinearEquiv

end SerrePositivity.BhattScholze

end PrismaticGeneratorPowerModPFaithful
