module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanTerminalRelativeHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful

/-!
概要：空間の元の単体的圏を、終対象上の left fibrations の単体的圏へ充満忠実に埋め込む。
方針：全内部 Hom の厳密な相対同型で射を移し、包含後の単位・合成の式で整合性を証明する。
規約：元の対象と全高次射を保持。coherent nerve 上での全充満忠実性を実証する。
使われ方：F1 の相対 Hom 分類を、空間の小さい全 Hom 関手へ前合成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 終対象射による、小さい Kan 対象の圏から left fibrations への全豊穣埋め込み。 -/
def kanTerminalEnriched :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (⊤_ SSet.{u})) where
  obj K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanTerminalObject K
  map K L := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj L.obj).inv
  map_id K := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    change (MonoidalClosed.id K.obj ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj K.obj).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj K.obj).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity (Over.mk (terminal.from K.obj)) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj K.obj).hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity_ι (Over.mk (terminal.from K.obj))).symm
  map_comp K L M := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    change (MonoidalClosed.comp K.obj L.obj M.obj ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj M.obj).inv) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj M.obj).hom =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj L.obj).inv ⊗ₘ
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso L.obj M.obj).inv) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (terminal.from K.obj))
              (Over.mk (terminal.from L.obj)) (Over.mk (terminal.from M.obj)) ≫
                (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj M.obj).hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι]
    change MonoidalClosed.comp K.obj L.obj M.obj =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj L.obj).inv ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso L.obj M.obj).inv) ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj L.obj).hom ⊗ₘ
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso L.obj M.obj).hom)) ≫ MonoidalClosed.comp K.obj L.obj M.obj
    rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
      tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- 同じ全豊穣埋め込みの、元の空間 ∞ 圏上の coherent nerve。 -/
def kanTerminalInfinity : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (⊤_ SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap kanTerminalEnriched

/-- 元の空間の全写像空間は、同じ終対象上の相対写像空間と同値。 -/
lemma kanTerminalInfinity_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful kanTerminalInfinity.{u} := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff kanTerminalEnriched).mpr
  intro K L
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalRelativeHomIso K.obj L.obj).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
