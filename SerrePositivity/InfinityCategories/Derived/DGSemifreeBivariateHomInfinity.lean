module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorProductMap
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTensorValue
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeIso
/-!
概要：元の導来 ∞ 圏の実反対と元の圏の直積から、同じ D(R) 値 Hom の全 ∞ 関手を作る。
方針：全 HA を持つ tensor 単体の実写像と、同じ実出力分解の ∞ 関手を合成する。
規約：元の出力の射影性を仮定しない。使われ方：二変数 Hom と固定入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory Opposite
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
def dgSemifreeDerivedHomProductDGopInfinity :
    dgNerve R (SemifreeDGModules R D)ᵒᵖ ⊗ dgModuleDerivedInfinityCategory R D ⟶
      dgHomDerivedNerve R D :=
  dgNerveTensorProductMap R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) ≫
    dgSemifreeDerivedHomTensorInfinity R D
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
def dgSemifreeDerivedHomBivariateInfinity :
    (dgModuleDerivedInfinityCategory R D).op ⊗ dgModuleDerivedInfinityCategory R D ⟶
      dgHomDerivedNerve R D :=
  ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom ⊗ₘ 𝟙 _) ≫
    dgSemifreeDerivedHomProductDGopInfinity R D
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
lemma dgSemifreeDerivedHomProductDGopInfinity_app {n : ℕ}
    (s : Simplex R (SemifreeDGModules R D)ᵒᵖ n) (t : Simplex R (SemifreeDGModules R D) n) :
    (dgSemifreeDerivedHomProductDGopInfinity R D).app (op ⦋n⦌) (s, t) =
      (dgSemifreeDerivedHomTensorInfinity R D).app (op ⦋n⦌)
        (dgNerveTensorSimplex R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) s t) := rfl
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
lemma dgSemifreeDerivedHomBivariateInfinity_vertex (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomBivariateInfinity R D).app (op ⦋0⦌)
      (SSet.opObjEquiv.symm (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌),
        Simplex.vertex Q) =
      Simplex.vertex ((dgUniverseLiftUp R (SemifreeDGModules R PUnit.{1})).obj
        (dgSemifreeDerivedHomTensorValue R D P Q)) := by
  change (dgSemifreeDerivedHomTensorInfinity R D).app (op ⦋0⦌)
    (dgNerveTensorSimplex R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D)
      ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom.app (op ⦋0⦌)
        (SSet.opObjEquiv.symm (Simplex.vertex P))) (Simplex.vertex Q)) = _
  rw [dgNerveOppositeIso_hom_vertex, dgNerveTensorSimplex_vertex]
  exact dgSemifreeDerivedHomTensorInfinity_vertex R D P Q

end SerrePositivity.InfinityCategories
