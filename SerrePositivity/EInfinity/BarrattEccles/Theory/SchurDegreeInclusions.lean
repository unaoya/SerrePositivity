module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeDecomposition

/-!
# Schur の次数分解と指定包含の比較

## 概要
Berger–Moerdijk §1 の Schur 表示の生成射を、arity と双次数の余不変の包含で読む。

## 方針
次数評価の余極限保存と、指定した余極限同型の計算則を使う。

## 規約
指定された斉次テンソルの包含を保つ。

## 使われ方
セルの語の基底を実際の演算の値へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- The Schur arity inclusion maps to its specified arity quotient and coproduct inclusion. -/
@[reassoc]
lemma schurι_degree_arity_hom (P : SymmetricSequence (Complex A))
    (K : Complex A) (i : ℤ) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i ≫ (schurDegreeArityIso P K i).hom =
      arityDiagramQuotient
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) n ≫
        Sigma.ι (arityDiagramCoinvariants
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i)) n := by
  let E := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let F := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K
  change E.map (colimit.ι F (FiniteBijection.of n)) ≫
    ((preservesColimitIso E F).hom ≫
      ((colimit.isColimit (F ⋙ E)).coconePointUniqueUpToIso
        (arityDiagramCoconeIsColimit (F ⋙ E))).hom) = _
  rw [← Category.assoc, ι_preservesColimitIso_hom]
  erw [IsColimit.comp_coconePointUniqueUpToIso_hom]
  simp only [arityDiagramCocone, FiniteBijection.card_of, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

section Tensor
variable {G : Type u} [Group G] {K L : Complex A}
  (ρ : G →* End K) (σ : G →* End L) (i : ℤ)

/-- Each bidegree coinvariant leg is the specified leg of the coinvariant coproduct. -/
@[reassoc]
lemma tensorDegreeCoinvariants_leg_hom (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    (Rep.coinvariantsFunctor A G).map (tensorDegreeRepresentationLeg ρ σ i a) ≫
      (tensorDegreeCoinvariantsIso ρ σ i).hom =
        Sigma.ι (fun a => ModuleCat.of A
          (tensorDegreeRepresentationSummand ρ σ i a).ρ.Coinvariants) a := by
  let F := Rep.coinvariantsFunctor A G
  let h := isColimitCofanMkObjOfIsColimit F (tensorDegreeRepresentationSummand ρ σ i)
    (tensorDegreeRepresentationLeg ρ σ i) (tensorDegreeRepresentationIsColimit ρ σ i)
  exact IsColimit.comp_coconePointUniqueUpToIso_hom h
    (colimit.isColimit (Discrete.functor _)) (Discrete.mk a)

end Tensor

/-- Taking the arity quotient commutes with inclusion of a homogeneous tensor. -/
@[reassoc]
lemma schurBidegree_quotient_naturality (P : SymmetricSequence (Complex A))
    (K : Complex A) (i : ℤ) (n : ℕ) (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    ιTensorObj (P.level n) (TensorPowers.power K n) a.1.1 a.1.2 i a.2 ≫
      arityDiagramQuotient
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) n =
    ModuleCat.ofHom (Representation.Coinvariants.mk
      (schurArityBidegreeRepresentation P K i n a).ρ) ≫
      (Rep.coinvariantsFunctor A (ULift.{u} (Equiv.Perm (Fin n)))).map
        (tensorDegreeRepresentationLeg (finiteBijectionComplexAction P n)
          (finiteBijectionComplexAction (TensorPowers.bijectionFunctor K) n) i a) := by
  exact (Rep.coinvariantsMk A (ULift.{u} (Equiv.Perm (Fin n)))).naturality
    (tensorDegreeRepresentationLeg (finiteBijectionComplexAction P n)
      (finiteBijectionComplexAction (TensorPowers.bijectionFunctor K) n) i a)

/-- A homogeneous Schur generator maps to its specified arity and bidegree quotient. -/
@[reassoc]
lemma schurBidegree_inclusion_hom (P : SymmetricSequence (Complex A))
    (K : Complex A) (i : ℤ) (n : ℕ) (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    ιTensorObj (P.level n) (TensorPowers.power K n) a.1.1 a.1.2 i a.2 ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i ≫ (schurDegreeBidegreeIso P K i).hom =
    ModuleCat.ofHom (Representation.Coinvariants.mk
      (schurArityBidegreeRepresentation P K i n a).ρ) ≫
      Sigma.ι (fun a => ModuleCat.of A
        (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants) a ≫
      Sigma.ι (fun n => ∐ (fun a => ModuleCat.of A
        (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants)) n := by
  simp only [schurDegreeBidegreeIso, Iso.trans_hom]
  rw [schurι_degree_arity_hom_assoc, Sigma.ι_mapIso_hom,
    ← Category.assoc, ← Category.assoc, schurBidegree_quotient_naturality]
  simp only [Category.assoc]
  erw [tensorDegreeCoinvariants_leg_hom_assoc]
  rfl

/-- The inverse degree decomposition sends a homogeneous quotient class to the Schur generator. -/
lemma schurBidegree_inclusion_inv (P : SymmetricSequence (Complex A))
    (K : Complex A) (i : ℤ) (n : ℕ) (a : {a : ℤ × ℤ // a.1 + a.2 = i})
    (u : (P.level n).X a.1.1) (v : (TensorPowers.power K n).X a.1.2) :
    (schurDegreeBidegreeIso P K i).inv
      (Sigma.ι (fun n => ∐ (fun a => ModuleCat.of A
        (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants)) n
        (Sigma.ι (fun a => ModuleCat.of A
          (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants) a
          (Representation.Coinvariants.mk
            (schurArityBidegreeRepresentation P K i n a).ρ (u ⊗ₜ[A] v)))) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i
        (ιTensorObj (P.level n) (TensorPowers.power K n) a.1.1 a.1.2 i a.2 (u ⊗ₜ[A] v)) := by
  apply (schurDegreeBidegreeIso P K i).toLinearEquiv.injective
  change ((schurDegreeBidegreeIso P K i).inv ≫ (schurDegreeBidegreeIso P K i).hom) _ =
    (ιTensorObj (P.level n) (TensorPowers.power K n) a.1.1 a.1.2 i a.2 ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n).f i ≫ (schurDegreeBidegreeIso P K i).hom) _
  rw [Iso.inv_hom_id, schurBidegree_inclusion_hom]
  rfl

end SerrePositivity.EInfinity
