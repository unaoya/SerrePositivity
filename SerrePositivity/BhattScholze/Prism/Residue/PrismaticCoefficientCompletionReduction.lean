module

public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticCoefficientQuotientComposition

/-! # 正則主元の完備化単位の二生成係数商還元

a,dを個別に正則とする場合にも、d mod aの正則性は仮定しない。
-/

@[expose] public noncomputable section
universe u
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
