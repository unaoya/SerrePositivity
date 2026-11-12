module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.EpsilonCellHomotopy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.NativeTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ChoiceInvariant

/-!
概要：固定 resolved 族の native ε core への作用に必要な対象等号。
方針：工程 1 の指定頂点比較を、cell ε core の可逆比較の剛性に代入する。
規約：この必要条件の固定族での成立・不成立も、最終 map の不存在も未主張。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] [Nontrivial R]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
  (A B : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ
local notation "IB" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R B κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "CB" => DGKappaCone R B IB
local notation "PA" => Source R CA
local notation "PB" => Source R CB
local notation "SA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)
local notation "SB" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CB (dgKappaConePerfectObjects R B IB)

/-- 工程 1 の頂点を ε core 内で比較しても、null 対象上の像は実際の対象として一致する必要がある。 -/
lemma dgSuspensionResolved_obj_eq_of_nativeHom
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
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B g))
    (b : SA) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).resolved.obj b.val =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).resolved.obj b.val :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonCell_nativeMap_obj_eq R PA CB SA SB b H
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonObject R κ hκ A B f)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonObject R κ hκ A B g) e hf hg

/-- 同じ resolved 対象への着地は、選択前の実加群延長の同型を要求する。 -/
def dgSuspensionExtensionIsoOfResolvedObjEq
    (f g : A ⟶ B) (M : CA)
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).resolved.obj (⟨M⟩ : PA) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).resolved.obj (⟨M⟩ : PA)) :
    (dgModuleExtension R A B f.down).onClosed.obj M.val ≅
      (dgModuleExtension R A B g.down).onClosed.obj M.val := by
  let IF := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R A B f.down hκ Fact.out
  let IG := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R A B g.down hκ Fact.out
  have he : (IF.obj M).val = (IG.obj M).val :=
    congrArg (fun x : PB => x.val.val) h
  exact IF.iso M ≪≫ eqToIso he ≪≫ (IG.iso M).symm

/-- 固定 resolved 族の対象等号は、選択前の実延長像の dg 同型と同値。 -/
lemma dgSuspensionResolved_obj_eq_iff_extensionIso (f g : A ⟶ B) (M : CA) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).resolved.obj (⟨M⟩ : PA) =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).resolved.obj (⟨M⟩ : PA) ↔
      Nonempty ((dgModuleExtension R A B f.down).onClosed.obj M.val ≅
        (dgModuleExtension R A B g.down).onClosed.obj M.val) := by
  constructor
  · intro h
    exact ⟨dgSuspensionExtensionIsoOfResolvedObjEq R κ hκ A B f g M h⟩
  · rintro ⟨a⟩
    letI : Nonempty κ.ord.ToType :=
      Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
    letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
        (dgModuleExtension R A B f.down).onClosed :=
      (dgModuleExtensionRestrictionAdjunction R A B f.down).leftAdjoint_preservesColimits
    letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
        (dgModuleExtension R A B g.down).onClosed :=
      (dgModuleExtensionRestrictionAdjunction R A B g.down).leftAdjoint_preservesColimits
    have he : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).cone.obj M =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).cone.obj M :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgProjectiveClosureFunctor_obj_eq_of_iso_at
        (R := R) (C := A) (D := B)
        (F := dgModuleExtension R A B f.down) (G := dgModuleExtension R A B g.down)
        (hO := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ Fact.out)
        (B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R A κ)
        (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R B κ)
        (hBF := fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R f.down i,
          ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereFreeExtensionIso R A B f.down i⟩⟩)
        (hBG := fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R g.down i,
          ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereFreeExtensionIso R A B g.down i⟩⟩) M a
    exact congrArg (fun x : CB => (⟨x⟩ : PB)) he

/-- 工程 1 と頂点比較があれば、各 null 代表の選択前の延長像まで実同型になる。 -/
def dgSuspensionExtensionIsoOfNativeHom
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
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A B g)) (b : SA) :
    (dgModuleExtension R A B f.down).onClosed.obj b.val.val.val ≅
      (dgModuleExtension R A B g.down).onClosed.obj b.val.val.val :=
  dgSuspensionExtensionIsoOfResolvedObjEq R κ hκ A B f g b.val.val
    (dgSuspensionResolved_obj_eq_of_nativeHom R κ hκ A B H f g e hf hg b)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
