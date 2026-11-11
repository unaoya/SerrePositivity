module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModulePiZeroBoundary
/-!
概要：正規化 Moore の実 H₀ と同じ境界商の自然同型。
方針：実辺・正規化の包含・標準ホモロジー射の可換式を使う。
規約：元の正規化射を保持する。使われ方：β5(g) の弱同値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite HomologicalComplex
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (W : SimplicialObject (ModuleCat.{v} S))
variable {V : SimplicialObject (ModuleCat.{v} S)}
def moduleMooreDegreeZeroIso :
    ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).X 0 ≅ W.obj (op ⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W 0 ≪≫ (Submodule.topEquiv :
    (⊤ : Submodule S (W.obj (op ⦋0⦌))) ≃ₗ[S] W.obj (op ⦋0⦌)).toModuleIso
lemma moduleMooreDegreeZeroIso_value
    (z : ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).X 0) :
    (moduleMooreDegreeZeroIso W).hom.hom z =
      (NormalizedMooreComplex.objX W 0).arrow.hom z := rfl
lemma moduleMooreDegreeZeroIso_range :
    (LinearMap.range
      (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d 1 0).hom).map
        (moduleMooreDegreeZeroIso W).toLinearEquiv.toLinearMap =
      LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap W) := by
  have hd (t : ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).X 1) :
      (moduleMooreDegreeZeroIso W).hom.hom
        ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d 1 0).hom t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap W ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W 1).hom.hom t) :=
    congrArg (fun ψ ↦ ψ.hom t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernel_d_arrow W 0)
  ext z
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W 1).hom.hom t, (hd t).symm⟩
  · rintro ⟨t, rfl⟩
    let u := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W 1).inv.hom t
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    exact (hd u).trans (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap W)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W 1).inv_hom_id_apply t))
def moduleMooreZeroHomologyIso :
    ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homology 0 ≅
      ModuleCat.of S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryQuotient W) :=
  ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).isoHomologyι₀ ≪≫
    ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).opcyclesIsoSc'
      1 0 0 (by simp) (by simp) ≪≫
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).sc' 1 0 0).moduleCatOpcyclesIso ≪≫
    (Submodule.Quotient.equiv _ _ (moduleMooreDegreeZeroIso W).toLinearEquiv
      (moduleMooreDegreeZeroIso_range W)).toModuleIso
lemma moduleMooreZeroHomologyIso_pOpcycles :
    ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).pOpcycles 0 ≫
      ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).isoHomologyι₀.inv ≫
        (moduleMooreZeroHomologyIso W).hom =
    (moduleMooreDegreeZeroIso W).hom ≫
      ModuleCat.ofHom (LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap W)).mkQ := by
  simp only [moduleMooreZeroHomologyIso, Iso.trans_hom,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc, HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom]
  simp only [ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl
variable {W}
lemma moduleMooreDegreeZeroIso_naturality (f : W ⟶ V) :
    ((normalizedMooreComplex (ModuleCat.{v} S)).map f).f 0 ≫
      (moduleMooreDegreeZeroIso V).hom =
    (moduleMooreDegreeZeroIso W).hom ≫ f.app (op ⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.normalizedMooreMap_arrow f 0
lemma moduleMooreZeroHomologyIso_naturality (f : W ⟶ V) :
    HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} S)).map f) 0 ≫
      (moduleMooreZeroHomologyIso V).hom =
    (moduleMooreZeroHomologyIso W).hom ≫ ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryQuotientMap f) := by
  let K := (normalizedMooreComplex (ModuleCat.{v} S)).obj W
  let L := (normalizedMooreComplex (ModuleCat.{v} S)).obj V
  let F := (normalizedMooreComplex (ModuleCat.{v} S)).map f
  have hp : (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫
      HomologicalComplex.homologyMap F 0 =
    F.f 0 ≫ (L.pOpcycles 0 ≫ L.isoHomologyι₀.inv) := by
    rw [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
      ← Category.assoc, HomologicalComplex.p_opcyclesMap, Category.assoc]
  have hq : f.app (op ⦋0⦌) ≫
      ModuleCat.ofHom (LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap V)).mkQ =
    ModuleCat.ofHom (LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryMap W)).mkQ ≫
      ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleZeroBoundaryQuotientMap f) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  apply (cancel_epi (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv)).mp
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [moduleMooreZeroHomologyIso_pOpcycles]
  conv_lhs => rw [← Category.assoc, moduleMooreDegreeZeroIso_naturality, Category.assoc, hq]
  conv_rhs =>
    rw [← Category.assoc, ← Category.assoc]
    arg 1
    rw [Category.assoc, moduleMooreZeroHomologyIso_pOpcycles]
  simp only [Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
