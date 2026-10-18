module

public import SerrePositivity.KST.DerivedBlowup.ExteriorComplexMap
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
概要：KST Def3.1 の整数次数外積複体の各項を総外積代数へ埋め込む。
方針：零延長の標準同型を第n外積の包含と合成する。
規約：まず次数−nについて構成する。次数0から正次数への微分は零。
使われ方：Koszul の積と chain map の等式を総外積代数上で検証する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：整数次数−nの項から総外積代数への線形包含。
方針：標準同型で第n外積へ戻し部分加群に含める。
規約：KST Def3.1。使われ方：次数別の積・微分の式を全外積で比較する。 -/
def exteriorCochainInclusionNeg (d : M →ₗ[R] R) (n : ℕ) :
    (exteriorKoszulCochain d).X (-(n : ℤ)) →ₗ[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.exteriorPower R n M).subtype.comp (exteriorKoszulCochainXIso d n).hom.hom

/-- 概要：各次数の項から総外積への包含は単射。
方針：同型の単射性と部分加群の包含の単射性を合成する。
規約：KST Def3.1。使われ方：総外積上での等式から複体成分の等式を得る。 -/
theorem exteriorCochainInclusionNeg_injective (d : M →ₗ[R] R) (n : ℕ) :
    Function.Injective (exteriorCochainInclusionNeg d n) := by
  exact Subtype.val_injective.comp
    ((ModuleCat.mono_iff_injective (exteriorKoszulCochainXIso d n).hom).mp inferInstance)

/-- 概要：整数次数の微分を第n外積へ戻すと収縮微分になる。
方針：零延長の微分比較と chain 複体の指定微分を使う。
規約：KST Def3.1、次数−n−1から−n。使われ方：Leibniz 則を整数 cochain 複体へ移す。 -/
theorem exteriorKoszulCochain_d_XIso (d : M →ₗ[R] R) (n : ℕ) :
    (exteriorKoszulCochain d).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (exteriorKoszulCochainXIso d n).hom =
      (exteriorKoszulCochainXIso d (n + 1)).hom ≫
        ModuleCat.ofHom (exteriorDegreeDifferential d n) := by
  have hd := (exteriorKoszulChain d).extend_d_eq (ComplexShape.embeddingUpIntLE 0)
    (i := n + 1) (j := n) (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ))
    (by simp) (by simp)
  change ((exteriorKoszulChain d).extend (ComplexShape.embeddingUpIntLE 0)).d
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ _ = _
  rw [hd]
  simp only [exteriorKoszulCochainXIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1
  simp only [exteriorKoszulChain, ChainComplex.of_d]

/-- 概要：整数次数の包含は微分と収縮を交換する。
方針：標準同型の微分比較を元で評価する。
規約：KST Def3.1、負次数の微分。使われ方：積の chain 条件の証明。 -/
theorem exteriorCochainInclusionNeg_d (d : M →ₗ[R] R) (n : ℕ)
    (z : (exteriorKoszulCochain d).X (-((n + 1 : ℕ) : ℤ))) :
    exteriorCochainInclusionNeg d n
        (((exteriorKoszulCochain d).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).hom z) =
      CliffordAlgebra.contractLeft (Q := 0) d (exteriorCochainInclusionNeg d (n + 1) z) := by
  have h := exteriorKoszulCochain_d_XIso d n
  exact congrArg (fun f :
      (exteriorKoszulCochain d).X (-((n + 1 : ℕ) : ℤ)) ⟶
        ModuleCat.of R (ExteriorAlgebra.exteriorPower R n M) => (f.hom z).val) h

/-- 概要：次数0の項の像に対する収縮は零。
方針：第0外積に属することを使う。
規約：KST Def3.1、微分の境界条件。使われ方：次数0を含む Leibniz 則。 -/
theorem exteriorCochainInclusionNeg_zero (d : M →ₗ[R] R)
    (z : (exteriorKoszulCochain d).X (-(0 : ℤ))) :
    CliffordAlgebra.contractLeft (Q := 0) d (exteriorCochainInclusionNeg d 0 z) = 0 :=
  exteriorContraction_zero_degree d _ ((exteriorKoszulCochainXIso d 0).hom.hom z).property

end SerrePositivity.KST.DerivedBlowup
