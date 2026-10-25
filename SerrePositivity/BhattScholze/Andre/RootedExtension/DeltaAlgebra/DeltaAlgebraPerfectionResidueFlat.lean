module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionTor
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # 実δ完全化の標準剰余テンソルの平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)

/-- 既存実δ完全化の標準剰余テンソルと、実各段の剰余テンソルのcolimitの同型。 -/
def deltaAlgebraPerfectionResidueColimitIso :
    colimit (deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀) ≅
      (ModuleCat.extendScalars q₀).obj M∞ :=
  (preservesColimitIso (ModuleCat.extendScalars q₀)
      (deltaAlgebraFrobeniusStageModuleDiagram E j)).symm ≪≫
    (ModuleCat.extendScalars q₀).mapIso (deltaAlgebraPerfectionModuleColimitIso E j)

/-- 元の実還元入力から、実δ完全化の同じ標準剰余テンソルの通常平坦性を得る。 -/
theorem deltaAlgebraPerfectionResidueTensor_flat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.Flat Q₀ ((ModuleCat.extendScalars q₀).obj M∞) := by
  let F := deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀
  let M := (ModuleCat.extendScalars q₀).obj M∞
  have ht (N : Type u) [AddCommGroup N] [Module Q₀ N] :
      Subsingleton (TorModule Q₀ 1 M N) := by
    let H := (Tor (ModuleCat Q₀) 1).obj (ModuleCat.of Q₀ N)
    let : PreservesColimitsOfShape ℕ H := tor_preservesSequentialColimits _ 1
    have hz : IsZero (colimit (F ⋙ H)) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply colimit.hom_ext
      intro k
      have hF := deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
        D E j d k hD hj hzero hFF
      let : Module.Flat Q₀ (F.obj k) := hF.1
      have : Subsingleton (TorModule Q₀ 1 (F.obj k) N) :=
        torModule_subsingleton_of_flat (F.obj k) N 0
      have : Subsingleton (TorModule Q₀ 1 N (F.obj k)) :=
        (torModuleComm (R := Q₀) 1 N (F.obj k)).injective.subsingleton
      have hzK : IsZero (H.obj (ModuleCat.of Q₀ (F.obj k))) :=
        ModuleCat.isZero_of_subsingleton _
      exact hzK.eq_of_src _ _
    have hlim : IsZero (H.obj (colimit F)) := hz.of_iso (preservesColimitIso H F)
    have hM : IsZero (H.obj M) :=
      hlim.of_iso (H.mapIso (deltaAlgebraPerfectionResidueColimitIso E j d)).symm
    have : Subsingleton (TorModule Q₀ 1 N M) := ModuleCat.subsingleton_of_isZero hM
    exact (torModuleComm (R := Q₀) 1 M N).injective.subsingleton
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  exact lTensor_injective_of_torModule_one M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range (ht (N' ⧸ f.range))

end SerrePositivity.BhattScholze
