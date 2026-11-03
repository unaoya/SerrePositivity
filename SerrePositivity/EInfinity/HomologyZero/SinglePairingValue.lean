module

public import SerrePositivity.EInfinity.HomologyZero.ZeroDegreeUnitValue
public import SerrePositivity.EInfinity.HomologyZero.PairingRepresentatives
public import SerrePositivity.HomologicalAlgebra.CochainSingleMonoidal
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# 離散複体の元の二入力射の単位値

概要：零次埋め込みで移した元の二入力加群射は、単位値上で同じ二入力射を与える。
方針：実 tensor 比較の零次純テンソル公式と標準 single 射の成分を使う。
規約：元の加群と射を保持し、標数・平坦性を仮定しない。
使われ方：離散 H⁰ 可換代数の積と標準複体同型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomologyZero
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped TensorProduct
variable {A : Type u} [CommRing A]

lemma singlePairing_value (M N L : ModuleCat.{u} A) (μ : M ⊗ N ⟶ L)
    (f : 𝟙_ (Complex A) ⟶ cochainSingleZero M)
    (g : 𝟙_ (Complex A) ⟶ cochainSingleZero N) :
    singleValue L (unitPairing ((cochainSingleTensorIso M N).hom ≫
      (CochainComplex.singleFunctor (ModuleCat A) 0).map μ) f g) =
      μ (singleValue M f ⊗ₜ[A] singleValue N g) := by
  unfold singleValue
  change (singleObjXSelf (.up ℤ) 0 L).hom
    (((cochainSingleTensorIso M N).hom ≫
      (CochainComplex.singleFunctor (ModuleCat A) 0).map μ).f 0
        ((((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A))) = _
  rw [unit_tensor_apply]
  change (singleObjXSelf (.up ℤ) 0 L).hom
    (((single (ModuleCat A) (.up ℤ) 0).map μ).f 0
      ((cochainSingleTensorIso M N).hom.f 0
        (ιTensorObj (cochainSingleZero M) (cochainSingleZero N) 0 0 0 rfl
          ((cycleFromUnit _ f).val ⊗ₜ[A] (cycleFromUnit _ g).val)))) = _
  rw [cochainSingleTensorIso_hom_apply_ι, single_map_f_self]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply]

end SerrePositivity.EInfinity.HomologyZero
