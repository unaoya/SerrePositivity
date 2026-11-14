module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionCofaces
public import SerrePositivity.HomologicalAlgebra.BicomplexProjectionNaturality
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionCofaces
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowFormsExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDegreeZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 完備分冪 de Rham の多項式代入の関手

## 概要
完備分冪 de Rham 双複体を多項式代数の厳密な関手にし、二つの軸射影の自然性を得る。

## 方針
恒等射と合成は、微分を保つ総外積の代数射の一意性で次数 0 に帰着する。

## 規約
軸射影の向きは総複体から第 0 行と第 0 列。

## 使われ方
BS 著者版 Theorem 6.4 の完備分冪 de Rham の比較。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.HomologicalAlgebra
open SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "F" => completedSubstitutionFunctor p γ hk hr
local notation "e" => substituteRowForms p γ hk hr
local notation "E" => substituteExterior p γ hk hr
local notation "D" => pdVerticalD p k
local notation "up" => ComplexShape.up ℕ

variable {Q Q' Q'' : Poly k} (f : Q ⟶ Q') (g : Q' ⟶ Q'')

private theorem completed_id (Q : Poly k) (n : ℕ) (x : pdTerm p k Q.n n) :
    substituteCompleted p γ hk hr (𝟙 Q) n x = x := by
  have h := congrArg (fun α => (α.app ⦋n⦌).right) ((F).map_id Q)
  exact ConcreteCategory.congr_hom h x

private theorem completed_comp (n : ℕ) (x : pdTerm p k Q.n n) :
    substituteCompleted p γ hk hr (f ≫ g) n x =
      substituteCompleted p γ hk hr g n (substituteCompleted p γ hk hr f n x) := by
  have h := congrArg (fun α => (α.app ⦋n⦌).right) ((F).map_comp f g)
  exact ConcreteCategory.congr_hom h x

omit [Fact p.Prime] in
private theorem zeroForm_hom_ext (n : ℕ)
    (a b : (pdRow p k Q.n 0).obj ⦋n⦌ ⟶ (pdRow p k Q'.n 0).obj ⦋n⦌)
    (h : ∀ x : pdTerm p k Q.n n,
      a (x ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm 1) =
        b (x ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm 1)) : a = b := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x w
  change pdTerm p k Q.n n at x
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm.surjective w
  have hc : (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm c =
      c • (exteriorPower.zeroEquiv k (CopyModule k Q.n ⦋n⦌)).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hc, ← TensorProduct.smul_tmul]
  exact h (c • x)

private theorem substitution_id (Q : Poly k) (n j : ℕ) : e (𝟙 Q) n j = 𝟙 _ := by
  refine rowForms_ext p Q Q.n n n (e (𝟙 Q) n) (fun _ => 𝟙 _) (E (𝟙 Q) n)
    (AlgHom.id k _) ?_ ?_ (fun j => substituteRowForms_d p γ hk hr (𝟙 Q) n j) ?_ ?_ j
  · exact map_inclusion p γ hk hr (𝟙 Q) n
  · intro i x
    rfl
  · intro i
    simp
  · apply zeroForm_hom_ext
    intro x
    change substituteForms p γ hk hr (𝟙 Q) n 0 _ = _
    rw [substituteForms_zero, completed_id]
    rfl

private theorem substitution_comp (n j : ℕ) :
    e (f ≫ g) n j = e f n j ≫ e g n j := by
  refine rowForms_ext p Q Q''.n n n (e (f ≫ g) n) (fun i => e f n i ≫ e g n i)
    (E (f ≫ g) n) ((E g n).comp (E f n)) ?_ ?_
    (fun i => substituteRowForms_d p γ hk hr (f ≫ g) n i) ?_ ?_ j
  · exact map_inclusion p γ hk hr (f ≫ g) n
  · intro i x
    simp only [ConcreteCategory.comp_apply, AlgHom.comp_apply]
    exact (map_inclusion p γ hk hr g n i (e f n i x)).trans
      (congrArg (fun x => E g n x) (map_inclusion p γ hk hr f n i x))
  · intro i
    rw [Category.assoc, substituteRowForms_d, ← Category.assoc,
      substituteRowForms_d, Category.assoc]
  · apply zeroForm_hom_ext
    intro x
    change substituteForms p γ hk hr (f ≫ g) n 0 _ =
      substituteForms p γ hk hr g n 0 (substituteForms p γ hk hr f n 0 _)
    rw [substituteForms_zero, substituteForms_zero, substituteForms_zero, completed_comp]

/-- 外次数を固定した余単体的な分冪形式の代入。 -/
def pdSubstitutionRow (j : ℕ) : pdRow p k Q.n j ⟶ pdRow p k Q'.n j where
  app n := e f n.len j
  naturality {m n} θ := by
    exact substituteRowForms_natural p θ γ hk hr f j

/-- 完備分冪 de Rham 双複体の多項式代入。 -/
def pdSubstitutionDoubleMap :
    pdDeRhamDoubleComplex p k Q.n ⟶ pdDeRhamDoubleComplex p k Q'.n := by
  refine HomologicalComplex₂.homMk (fun ij => e f ij.1 ij.2) ?_ ?_
  · intro a b j h
    exact (((alternatingCofaceMapComplex _).map (pdSubstitutionRow p γ hk hr f j)).comm a b)
  · intro a i j h
    obtain rfl : i + 1 = j := h
    change _ ≫ (pdDeRhamColumn p k Q'.n ⦋a⦌).d i (i + 1) =
      (pdDeRhamColumn p k Q.n ⦋a⦌).d i (i + 1) ≫ _
    rw [column_d_eq, column_d_eq]
    exact substituteRowForms_d p γ hk hr f a i

/-- 多項式代数上の完備分冪 de Rham 双複体の厳密な関手。 -/
def pdSubstitutionDoubleFunctor :
    Poly k ⥤ HomologicalComplex₂ (ModuleCat.{u} k) up up where
  obj Q := pdDeRhamDoubleComplex p k Q.n
  map f := pdSubstitutionDoubleMap p γ hk hr f
  map_id Q := by
    ext a b : 2
    exact substitution_id p γ hk hr Q a b
  map_comp f g := by
    ext a b : 2
    exact substitution_comp p γ hk hr f g a b

/-- 第 0 行での多項式代入。 -/
def pdSubstitutionRowZero :
    (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k Q.n 0) ⟶
      (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k Q'.n 0) :=
  bicomplexRowMap (pdSubstitutionDoubleMap p γ hk hr f) 0

/-- 第 0 列での多項式代入。 -/
def pdSubstitutionColumnZero :
    pdDeRhamColumn p k Q.n ⦋0⦌ ⟶ pdDeRhamColumn p k Q'.n ⦋0⦌ :=
  (pdSubstitutionDoubleMap p γ hk hr f).f 0

/-- 多項式代入は総複体から第 0 行への射影と可換。 -/
theorem pdSubstitution_rowProjection :
    HomologicalComplex₂.total.map (pdSubstitutionDoubleMap p γ hk hr f) up ≫
        pdDeRhamRowZeroProjection p k Q'.n =
      pdDeRhamRowZeroProjection p k Q.n ≫
        pdSubstitutionRowZero p γ hk hr f :=
  totalToRowZero_naturality _

/-- 多項式代入は総複体から第 0 列への射影と可換。 -/
theorem pdSubstitution_columnProjection :
    HomologicalComplex₂.total.map (pdSubstitutionDoubleMap p γ hk hr f) up ≫
        pdDeRhamColumnZeroProjection p k Q'.n =
      pdDeRhamColumnZeroProjection p k Q.n ≫ pdSubstitutionColumnZero p γ hk hr f :=
  totalToColumnZero_naturality _

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
