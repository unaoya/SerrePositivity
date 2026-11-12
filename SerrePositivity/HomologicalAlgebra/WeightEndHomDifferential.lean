module
public import SerrePositivity.HomologicalAlgebra.WeightEndHomEvaluation
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalDifferential
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRowDifferential

/-!
概要：積 end から零延長重みの Hom への符号付き比較が微分と可換であること。
方針：各横次数の成分を取り、縦横の二つの符号の漸化式を適用する。
規約：零次数の指定評価を保つ。内部次数の有界性は仮定しない。
使われ方：HA 1.2.4、G10 の Hom 空間との複体比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (K : ChainComplex (Jᵒᵖ ⥤ ModuleCat.{u} A) ℕ) (X : Jᵒᵖ ⥤ Complex A)

/-- 指定次数比較は実際の微分と可換。 -/
theorem weightEndHomComponentsEquiv_d (q : ℤ)
    (z : ((linearWeightEndTotalFunctor A X).obj (op K)).X q) :
    weightEndHomComponentsEquiv A K X (q+1)
      (((linearWeightEndTotalFunctor A X).obj (op K)).d q (q+1) z) =
    δ q (q+1) (weightEndHomComponentsEquiv A K X q z) := by
  let E := (linearWeightEndCochainFunctor A X).obj (op K)
  let H := (functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X
  apply (extendedChainHomRowsLinearEquiv K H A (q+1)).injective
  change extendedChainHomRows K H (q+1) _ = extendedChainHomRows K H (q+1) _
  funext n
  rw [weightEndHomComponentsEquiv_rows]
  cases n with
  | zero =>
    rw [weightEndHomSign_zero, one_smul, extendedChainHomRows_d_zero,
      weightEndHomComponentsEquiv_zero]
    have hd := congrArg (fun f => f z) (CochainProductTotal.component_d_zero E q)
    exact hd
  | succ n =>
    rw [extendedChainHomRows_d_succ, weightEndHomComponentsEquiv_rows,
      weightEndHomComponentsEquiv_rows]
    have hd := congrArg (fun f => f z) (CochainProductTotal.component_d_succ E n q)
    let v (m : ℕ) : K.X m ⟶ H.X (q-m) := CochainProductTotal.componentπ E m q z
    have hdeg : q-(n : ℤ) = q+1-(n+1 : ℕ) := by push_cast; omega
    change CochainProductTotal.componentπ E (n+1) (q+1)
      (((linearWeightEndTotalFunctor A X).obj (op K)).d q (q+1) z) =
      (eqToHom (by rw [hdeg]) :
        ModuleCat.of A (K.X (n+1) ⟶ H.X (q-n)) ⟶
        ModuleCat.of A (K.X (n+1) ⟶ H.X (q+1-(n+1 : ℕ))))
        (K.d (n+1) n ≫ v n) +
      ((n+1 : ℕ) : ℤ).negOnePow •
        (v (n+1) ≫
          H.d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ))) at hd
    have hc (p r : ℤ) (h : p=r) (f : K.X (n+1) ⟶ H.X p) :
        (eqToHom (by rw [h]) : ModuleCat.of A (K.X (n+1) ⟶ H.X p) ⟶
          ModuleCat.of A (K.X (n+1) ⟶ H.X r)) f =
          f ≫ eqToHom (by rw [h]) := by
      cases h
      rfl
    rw [hc _ _ hdeg] at hd
    have hs :
        weightEndHomSign (n+1) (q+1) •
          ((K.d (n+1) n ≫ v n) ≫ eqToHom (congrArg H.X hdeg) +
          ((n+1 : ℕ) : ℤ).negOnePow •
            (v (n+1) ≫ H.d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ)))) =
        (weightEndHomSign (n+1) q • v (n+1)) ≫
          H.d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ)) +
        (q+1).negOnePow •
          (K.d (n+1) n ≫ (weightEndHomSign n q • v n) ≫ eqToHom (congrArg H.X hdeg)) := by
      simp only [smul_add, Linear.units_smul_comp, Linear.comp_units_smul,
        smul_smul, weightEndHomSign_vertical]
      rw [weightEndHomSign_horizontal]
      exact add_comm _ _
    rw [hd]
    exact hs

end SerrePositivity.HomologicalAlgebra
