module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives

/-!
# 有限 Cartier 同型の代表元

## 概要
Cartier の加法同型の値を、その代表形式の de Rham 類として計算する。

## 方針
微分が零の複体のコホモロジーと項の同一視を、余輪体の代表で照合する。

## 規約
単項式基底の順序を `polynomialFormsBasis` とそろえる。

## 使われ方
逆 Cartier の生成元と外積の照合。
-/

public noncomputable section

open CategoryTheory HomologicalComplex Set

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [LinearOrder T]
variable (p : ℕ) [CharP K p] (hp : 0 < p)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteCartierLinearEquiv_class (j : ℕ) (x : forms K T j) :
    finiteCartierLinearEquiv K T p hp j x =
      deRhamClass K T j (cartierRep K T p hp j x) (by
        have h := DFunLike.congr_fun (rep_d_zero K T p hp j) x
        change (deRhamComplex K T).d j (j + 1)
          (deRhamTerm K T j (cartierRep K T p hp j x)) = 0 at h
        rw [deRhamTerm_d] at h
        exact (deRhamTerm K T (j + 1)).injective (h.trans (map_zero _).symm)) := by
  let Z := CartierComplex K T
  let C := deRhamComplex K T
  let F := repMap K T p hp
  let x' : Z.X j := x
  have hd (a b : ℕ) : Z.d a b = 0 := by
    by_cases h : a + 1 = b
    · subst b
      dsimp only [Z, CartierComplex, CochainComplex.of]
      rw [CochainComplex.of_d]
    · exact Z.shape a b h
  let S := Z.sc j
  let L := (ShortComplex.HomologyData.ofZeros S (hd _ _) (hd _ _)).left
  let e := L.homologyIso
  let z := Z.cyclesMk x' (j + 1) (CochainComplex.next ℕ j) (by rw [hd]; rfl)
  have hz : Z.iCycles j z = x' := Z.i_cyclesMk x' (j + 1) (CochainComplex.next ℕ j) _
  have he : e.inv x' = Z.homologyπ j z := by
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom L.homologyπ_comp_homologyIso_hom z
    have h₂ := ConcreteCategory.congr_hom L.cyclesIso_hom_comp_i z
    have h₃ := ConcreteCategory.congr_hom e.inv_hom_id x'
    change e.hom (Z.homologyπ j z) = L.cyclesIso.hom z at h₁
    change L.cyclesIso.hom z = Z.iCycles j z at h₂
    exact h₃.trans (h₁.trans (h₂.trans hz)).symm
  let ω := cartierRep K T p hp j x
  let w := C.cyclesMk (deRhamTerm K T j ω) (j + 1) (CochainComplex.next ℕ j) (by
    exact DFunLike.congr_fun (rep_d_zero K T p hp j) x)
  have hw : cyclesMap F j z = w := by
    apply (ModuleCat.mono_iff_injective (C.iCycles j)).mp inferInstance
    have h := ConcreteCategory.congr_hom (cyclesMap_i F j) z
    change C.iCycles j (cyclesMap F j z) = F.f j (Z.iCycles j z) at h
    rw [h, hz]
    exact (C.i_cyclesMk _ (j + 1) (CochainComplex.next ℕ j) _).symm
  change homologyMap F j (e.inv x') = C.homologyπ j w
  rw [he]
  have hn := ConcreteCategory.congr_hom (homologyπ_naturality F j) z
  change homologyMap F j (Z.homologyπ j z) = C.homologyπ j (cyclesMap F j z) at hn
  rw [hn, hw]

/-- 単項式外積の像は、Cartier 指数を持つ代表のコホモロジー類。 -/
theorem finiteCartierLinearEquiv_basis (j : ℕ) (m : T →₀ ℕ) (s : powersetCard T j) :
    finiteCartierLinearEquiv K T p hp j (polynomialFormsBasis K T j (m, s)) =
      deRhamClass K T j (polynomialFormsBasis K T j (cartierExponent T p m s, s))
        (polynomialFormsBasis_cartier_closed K T p (CharP.cast_eq_zero K p) _ _
          (cartierExponent_weight T p hp m s)) := by
  rw [finiteCartierLinearEquiv_class]
  congr 1
  exact rep_basis K T p hp j (m, s)

end SerrePositivity.DeRham
