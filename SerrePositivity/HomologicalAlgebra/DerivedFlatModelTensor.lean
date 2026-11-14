module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedTensorUnresolvedModule
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # Tensor vanishing for actual pure flat objects in any projective representative -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Tensoring with a flat module is concentrated in degree zero for every coefficient module. -/
lemma derivedTensorModule_homology_isZero_of_flat_right (M H : ModuleCat.{u} R)
    (hFlat : Module.Flat R H) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((boundedAboveDerivedTensorModuleFunctor M).obj H)) := by
  let hF := hFlat
  by_cases hp : 0 < i
  · exact DerivedCategory.isZero_of_isLE _ 0 i hp
  · let n := (-i).toNat
    have hn : 0 < n := by dsimp [n]; omega
    have he : i = -(n : ℤ) := by dsimp [n]; omega
    rw [he]
    have ht : Subsingleton (TorModule R n M H) := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [hj]
      let hT := torModule_subsingleton_of_flat (R := R) H M j
      exact (torModuleComm (R := R) (j + 1) M H).injective.subsingleton
    have hz : IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj H) :=
      ModuleCat.isZero_of_subsingleton _
    exact ((boundedAboveDerivedTensorModuleTorNatIso M n).app H).isZero_iff.mpr hz

/-- A pure flat actual object has no off-zero tensor homology in every fixed projective model. -/
lemma moduleTensorCochain_model_homology_isZero_of_pure_flat
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj)
    (hPure : ∀ j : ℤ, j ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj X.obj))
    (hFlat : Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj))
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i ≠ 0) :
    IsZero (((moduleTensorCochainFunctor P.complex).obj M).homology i) := by
  let hGE : X.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr
    (fun j hj ↦ hPure j (by omega))
  let hLE : X.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr
    (fun j hj ↦ hPure j (by omega))
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj
  let e : X ≅ boundedAboveDerivedSingleFunctor.obj H :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0)
  let eT := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl (boundedAboveDerivedSingleFunctor.obj M)) e))
  have ht : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (boundedAboveDerivedTensor.obj (boundedAboveDerivedSingleFunctor.obj M, X)).obj) :=
    (derivedTensorModule_homology_isZero_of_flat_right M H hFlat i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eT)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (derivedTensorUnresolvedModuleModelIso M X P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app
      ((moduleTensorCochainFunctor P.complex).obj M)).isZero_iff.mp ht

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.2.12" (partial := special) "仮定：通常の可換環 R と有界上導来対象、指定した射影模型（Lean が強い：通常環のこの導来模型の場合）。結論：全離散係数との模型テンソルが零次以外で消える条件から対象の離散性と H⁰ の平坦性を示し、逆に離散かつ平坦な H⁰ から同じ模型での消滅を示す（離散環上の平坦性のテンソル検査の部分に一致）。一般の環スペクトルの flat 述語との比較は含まれない。"] _root_.SerrePositivity.moduleTensorCochain_model_homology_isZero_of_pure_flat
