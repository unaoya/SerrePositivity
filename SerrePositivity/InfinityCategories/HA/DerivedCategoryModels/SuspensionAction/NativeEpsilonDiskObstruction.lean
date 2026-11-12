module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.NativeDiskPair
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.NativeRepresentableRequirement

/-!
概要：固定 sphere-closure data の頂点比較を持つ native ε 着地の具体的反例。
方針：零と非零可縮 disk への二つの点関手を、一セル null 代表で試験する。
規約：固定 ε core を経由する工程 1 の反例。最終 map の不存在は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

/-- 採用された対象宇宙の一対象環入力。 -/
def nativeDiskSourceInput : PerfDGInput.{u, max (u + 1) v} R :=
  perfDGInputOf R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.NativeDiskUnitInput.{max (u + 1) v}

/-- 採用された対象宇宙の零／disk 二対象入力。 -/
def nativeDiskTargetInput : PerfDGInput.{u, max (u + 1) v} R :=
  perfDGInputOf R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.NativeDiskPair.{max (u + 1) v}

/-- 零複体を選ぶ同じ厳密 dg 射。 -/
def nativeDiskZeroInputMap : nativeDiskSourceInput.{u,v} R ⟶ nativeDiskTargetInput.{u,v} R :=
  ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.nativeDiskPointFamily R).obj (ULift.up false))

/-- disk を選ぶ同じ厳密 dg 射。 -/
def nativeDiskNonzeroInputMap : nativeDiskSourceInput.{u,v} R ⟶ nativeDiskTargetInput.{u,v} R :=
  ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.nativeDiskPointFamily R).obj (ULift.up true))

/-- 二つの実入力射は、入力の正本 native Hom 内で可逆に結ばれる。 -/
def nativeDiskInputMapVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R
      (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R))
      (dgFunctorNativeMappingVertex R _ _ (nativeDiskZeroInputMap.{u,v} R).down)
      (dgFunctorNativeMappingVertex R _ _ (nativeDiskNonzeroInputMap.{u,v} R).down) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.nativeDiskPointVertexIso R

variable [Nontrivial R] (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 反例の試験に使う、固定 sphere-closure の同じ一セル null 対象。 -/
def nativeDiskNullSeed :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionRepresentableNullSeed R κ hκ (nativeDiskSourceInput.{u,v} R)
    (ULift.up PUnit.unit)

/-- 同じ sphere-closure data は、一セル null 代表を異なる実 cell 対象へ送る。 -/
lemma nativeDiskResolvedSeedImages_ne :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (nativeDiskZeroInputMap.{u,v} R)).resolved.obj
        (nativeDiskNullSeed.{u,v} R κ hκ).val ≠
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (nativeDiskNonzeroInputMap.{u,v} R)).resolved.obj
        (nativeDiskNullSeed.{u,v} R κ hκ).val := by
  intro h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.nativeDiskPair_no_closedIso R
    ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionInputObjectIsoOfResolvedSeedEq R κ hκ
      (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R)
      (nativeDiskZeroInputMap R) (nativeDiskNonzeroInputMap R) (ULift.up PUnit.unit) h⟩

/-- 固定 data の全頂点を ε core 内で比較する工程 1 は、この有限入力で存在しない。 -/
theorem no_nativeDiskSuspensionEpsilonHom :
    ¬ ∃ H : dgFunctorNativeMappingSpace R
        (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R) ⟶
          _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ
            (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R),
      ∀ f : nativeDiskSourceInput.{u,v} R ⟶ nativeDiskTargetInput.{u,v} R,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ
          (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R))
          (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R
            (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R) f.down))
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ
            (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R) f)) := by
  rintro ⟨H, hH⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.nativeDiskPair_no_closedIso R ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionInputObjectIsoOfNativeHom R κ hκ
    (nativeDiskSourceInput.{u,v} R) (nativeDiskTargetInput.{u,v} R) H
    (nativeDiskZeroInputMap R) (nativeDiskNonzeroInputMap R) (nativeDiskInputMapVertexIso R)
    (hH (nativeDiskZeroInputMap R)).some (hH (nativeDiskNonzeroInputMap R)).some
    (ULift.up PUnit.unit)⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
