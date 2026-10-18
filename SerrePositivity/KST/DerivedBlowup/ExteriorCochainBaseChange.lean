module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainBaseChangeComponents

/-!
概要：KST Def3.1 の整数次数 Koszul 外積複体の底変更同型。
方針：非正次数の標準同型で chain 微分比較へ帰着し、正次数は零対象性を使う。
規約：環準同型に沿う項別スカラー拡大。
使われ方：Koszul dg 代数の底変更比較の underlying cochain 同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：整数次数の底変更項同型は微分と可換。
方針：負次数では零延長の微分公式と chain 底変更同型を使う。
規約：KST Def3.1。使われ方：底変更 cochain 同型の組立て。 -/
theorem exteriorCochainBaseChangeXIso_comm (φ : R →+* S) (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d)).d q (q + 1) ≫
        (exteriorCochainBaseChangeXIso φ d (q + 1)).hom =
      (exteriorCochainBaseChangeXIso φ d q).hom ≫
        (baseChange φ (exteriorKoszulCochain d)).d q (q + 1) := by
  let := φ.toAlgebra
  cases q with
  | ofNat q =>
    exact ((ModuleCat.extendScalars φ).map_isZero
      (exteriorKoszulCochain_isZero_X_pos d (Int.ofNat q + 1)
        (by change 0 < (q : ℤ) + 1; omega))).eq_of_tgt _ _
  | negSucc n =>
    have hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    rw [hn]
    change (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d)).d
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (exteriorCochainBaseChangeXIso φ d (-(n : ℤ))).hom =
      (exteriorCochainBaseChangeXIso φ d (-((n + 1 : ℕ) : ℤ))).hom ≫
        (ModuleCat.extendScalars φ).map
          ((exteriorKoszulCochain d).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)))
    have hd (δ : M →ₗ[R] R) := HomologicalComplex.extend_d_eq (exteriorKoszulChain δ)
      (ComplexShape.embeddingUpIntLE 0) (i := n + 1) (j := n)
      (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ))
      (by simp only [ComplexShape.embeddingUpIntLE_f, zero_sub])
      (by simp only [ComplexShape.embeddingUpIntLE_f, zero_sub])
    have hds := HomologicalComplex.extend_d_eq
      (exteriorKoszulChain (exteriorBaseChangeDifferential (S := S) d))
      (ComplexShape.embeddingUpIntLE 0) (i := n + 1) (j := n)
      (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ))
      (by simp only [ComplexShape.embeddingUpIntLE_f, zero_sub])
      (by simp only [ComplexShape.embeddingUpIntLE_f, zero_sub])
    change (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d)).d
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (exteriorKoszulCochainXIso (exteriorBaseChangeDifferential (S := S) d) (n + 1)).hom ≫
          (exteriorKoszulChain (exteriorBaseChangeDifferential (S := S) d)).d (n + 1) n ≫
            (exteriorKoszulCochainXIso (exteriorBaseChangeDifferential (S := S) d) n).inv at hds
    have hdr := hd d
    change (exteriorKoszulCochain d).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (exteriorKoszulCochainXIso d (n + 1)).hom ≫ (exteriorKoszulChain d).d (n + 1) n ≫
        (exteriorKoszulCochainXIso d n).inv at hdr
    rw [hds, hdr, exteriorCochainBaseChangeXIso_neg, exteriorCochainBaseChangeXIso_neg]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc]
    exact congrArg (fun f =>
      (exteriorKoszulCochainXIso (exteriorBaseChangeDifferential (S := S) d) (n + 1)).hom ≫
        f ≫ (ModuleCat.extendScalars φ).map (exteriorKoszulCochainXIso d n).inv)
      ((exteriorChainBaseChangeIso φ d).hom.comm (n + 1) n).symm

/-- 概要：Koszul 外積 cochain 複体はスカラー拡大と可換。
方針：次数別同型と微分比較を既存複体同型 constructor へ渡す。
規約：KST Def3.1、任意可換環間の環準同型。
使われ方：dg チャートの係数変更と導来比較。 -/
def exteriorCochainBaseChangeIso (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d) ≅
      baseChange φ (exteriorKoszulCochain d) := by
  letI := φ.toAlgebra
  refine HomologicalComplex.Hom.isoOfComponents (exteriorCochainBaseChangeXIso φ d) ?_
  intro i j hij
  obtain rfl : j = i + 1 := hij.symm
  exact (exteriorCochainBaseChangeXIso_comm φ d i).symm

end SerrePositivity.KST.DerivedBlowup
