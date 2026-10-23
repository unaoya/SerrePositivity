module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanTerminalRelativeHom
public import SerrePositivity.InfinityCategories.F1.CoherentNerveFullyFaithful

/-!
概要：空間の元の単体的圏を、終対象上の left fibrations の単体的圏へ充満忠実に埋め込む。
方針：全内部 Hom の厳密な相対同型で射を移し、包含後の単位・合成の式で整合性を証明する。
規約：元の対象と全高次射を保持。coherent nerve 上での全充満忠実性を実証する。
使われ方：F1 の相対 Hom 分類を、空間の小さい全 Hom 関手へ前合成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 終対象射による、小さい Kan 対象の圏から left fibrations への全豊穣埋め込み。 -/
def kanTerminalEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} (LeftFibrationObject (⊤_ SSet.{u})) where
  obj K := kanTerminalObject K
  map K L := (terminalRelativeHomIso K.obj L.obj).inv
  map_id K := by
    apply vertexFiber_hom_ext
    change (MonoidalClosed.id K.obj ≫ (terminalRelativeHomIso K.obj K.obj).inv) ≫
      (terminalRelativeHomIso K.obj K.obj).hom =
        relativeFunctorIdentity (Over.mk (terminal.from K.obj)) ≫
          (terminalRelativeHomIso K.obj K.obj).hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (relativeFunctorIdentity_ι (Over.mk (terminal.from K.obj))).symm
  map_comp K L M := by
    apply vertexFiber_hom_ext
    change (MonoidalClosed.comp K.obj L.obj M.obj ≫
      (terminalRelativeHomIso K.obj M.obj).inv) ≫ (terminalRelativeHomIso K.obj M.obj).hom =
        ((terminalRelativeHomIso K.obj L.obj).inv ⊗ₘ
          (terminalRelativeHomIso L.obj M.obj).inv) ≫
            relativeFunctorComposition (Over.mk (terminal.from K.obj))
              (Over.mk (terminal.from L.obj)) (Over.mk (terminal.from M.obj)) ≫
                (terminalRelativeHomIso K.obj M.obj).hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [relativeFunctorComposition_ι]
    change MonoidalClosed.comp K.obj L.obj M.obj =
      (((terminalRelativeHomIso K.obj L.obj).inv ⊗ₘ
        (terminalRelativeHomIso L.obj M.obj).inv) ≫
          ((terminalRelativeHomIso K.obj L.obj).hom ⊗ₘ
            (terminalRelativeHomIso L.obj M.obj).hom)) ≫ MonoidalClosed.comp K.obj L.obj M.obj
    rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
      tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- 同じ全豊穣埋め込みの、元の空間 ∞ 圏上の coherent nerve。 -/
def kanTerminalInfinity : SpaceInfinity.{u} ⟶ LeftFibrationInfinity (⊤_ SSet.{u}) :=
  coherentNerveMap kanTerminalEnriched

/-- 元の空間の全写像空間は、同じ終対象上の相対写像空間と同値。 -/
lemma kanTerminalInfinity_isFullyFaithful : IsFullyFaithful kanTerminalInfinity.{u} := by
  apply (coherentNerveMap_isFullyFaithful_iff kanTerminalEnriched).mpr
  intro K L
  exact (qCatEquivalenceOfIso (terminalRelativeHomIso K.obj L.obj).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Presentable
