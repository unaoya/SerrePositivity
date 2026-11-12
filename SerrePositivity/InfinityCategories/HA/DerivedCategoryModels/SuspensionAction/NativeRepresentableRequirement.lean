module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.NativeEpsilonRequirement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.RepresentableSeed

/-!
概要：固定 ε core への工程 1 が、元の代表加群の実同型まで要求することを示す。
方針：同じ sphere-free 基底の一セル代表を null 対象として試験する。
規約：最終 map の非存在を主張せず、現在の ε 着地経路の必要条件を検査する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A B : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "PA" => Source R CA
local notation "SA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)

/-- 元の代表加群と実同型な、同じ閉包集合内の指定一セル代表。 -/
def dgSuspensionRepresentableSeed (x : A) : CA :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIndex A hκ x),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeed_mem R A hκ x⟩

/-- 一セル代表は、正本 cone の零化対象集合に属する。 -/
lemma dgSuspensionRepresentableSeed_perfect (x : A) :
    dgSuspensionRepresentableSeed R κ hκ A x ∈ dgKappaConePerfectObjects R A IA :=
  (modulePerfect R A).prop_of_iso
    ((moduleToDerived R A).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIso R A hκ x)).symm
    (modulePerfectOver_representable R A x (Set.mem_univ x))

/-- 同じ分解内に持つ null 対象。 -/
def dgSuspensionRepresentableNullSeed (x : A) : SA :=
  ⟨⟨dgSuspensionRepresentableSeed R κ hκ A x⟩,
    dgSuspensionRepresentableSeed_perfect R κ hκ A x⟩

/-- 工程 1 の ε 着地と頂点比較は、入力の可逆比較を実代表加群同型へ送る必要がある。 -/
def dgSuspensionRepresentableIsoOfNativeHom [Nontrivial R]
    (H : dgFunctorNativeMappingSpace R A B ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
    (f g : A ⟶ B)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B f.down))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B f))
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B g.down))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B g)) (x : A) :
    ForgetEnrichment.of (Complex R) (representable R (f.down.obj x)) ≅
      ForgetEnrichment.of (Complex R) (representable R (g.down.obj x)) := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIso R A hκ x
  let m := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionExtensionIsoOfNativeHom R κ hκ A B H f g e hf hg
    (dgSuspensionRepresentableNullSeed R κ hκ A x)
  change (dgModuleExtension R A B f.down).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIndex A hκ x)) ≅
    (dgModuleExtension R A B g.down).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIndex A hκ x)) at m
  let af := (dgModuleExtension R A B f.down).onClosed.mapIso s ≪≫
    dgModuleExtensionRepresentableIso R A B f.down x
  let ag := (dgModuleExtension R A B g.down).onClosed.mapIso s ≪≫
    dgModuleExtensionRepresentableIso R A B g.down x
  exact af.symm ≪≫ m ≪≫ ag

/-- 一セル代表での resolved 像対象の等号から、元対象の実閉射同型を回収する。 -/
def dgSuspensionInputObjectIsoOfResolvedSeedEq [Nontrivial R]
    (f g : A ⟶ B) (x : A)
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).resolved.obj
        (⟨dgSuspensionRepresentableSeed R κ hκ A x⟩ : PA) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).resolved.obj
        (⟨dgSuspensionRepresentableSeed R κ hκ A x⟩ : PA)) :
    ForgetEnrichment.of (Complex R) (f.down.obj x) ≅
      ForgetEnrichment.of (Complex R) (g.down.obj x) := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIso R A hκ x
  let m := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionExtensionIsoOfResolvedObjEq R κ hκ A B f g
    (dgSuspensionRepresentableSeed R κ hκ A x) h
  change (dgModuleExtension R A B f.down).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIndex A hκ x)) ≅
    (dgModuleExtension R A B g.down).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaRepresentableSeedIndex A hκ x)) at m
  let af := (dgModuleExtension R A B f.down).onClosed.mapIso s ≪≫
    dgModuleExtensionRepresentableIso R A B f.down x
  let ag := (dgModuleExtension R A B g.down).onClosed.mapIso s ≪≫
    dgModuleExtensionRepresentableIso R A B g.down x
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgRepresentableReflectIso R B (af.symm ≪≫ m ≪≫ ag)

/-- 同じ ε 着地経路は、入力の可逆比較を元の対象の厳密な閉射同型へ反映する。 -/
def dgSuspensionInputObjectIsoOfNativeHom [Nontrivial R]
    (H : dgFunctorNativeMappingSpace R A B ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
    (f g : A ⟶ B)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B f.down))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B f))
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B g.down))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B g)) (x : A) :
    ForgetEnrichment.of (Complex R) (f.down.obj x) ≅
      ForgetEnrichment.of (Complex R) (g.down.obj x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgRepresentableReflectIso R B
    (dgSuspensionRepresentableIsoOfNativeHom R κ hκ A B H f g e hf hg x)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
