module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitTransportComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaSectionInitialUnit
public import SerrePositivity.InfinityCategories.F1B.UnitMappingAdjunction

/-!
概要：各 comma の始対象から指定単位の写像空間の普遍性と ∞ 随伴を構成する。
方針：同じ始対象からの普遍輸送の同値性を、元の単位比較へ反映する。
規約：全パラメータの単位 Hom の全単射は仮定しない。
使われ方：HTT §5.2.2 の局所存在判定、局所置換から反射への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- comma の指定単位の始対象性から、元の標準区間比較そのものの同値性が従う。 -/
lemma unitIntervalMap_isQCatEquivalence_of_commaInitial
    (η : FunctorHom (𝟙 X) (F ≫ G)) (hη : UnitCommaInitialCondition η)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) : IsQCatEquivalence (unitIntervalMap η x y) := by
  have hi := (unitCommaInitialCondition_iff η).mp hη x
  have ht := parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialFiberPoint
    (F1B.kanUnitCommaFiberProjection G x) (F.app (Opposite.op ⦋0⦌) x) y
    (unitCommaSectionTargetFiberVertex η x) hi
  have he := (qCatEquivalenceOfIso (F1B.kanUnitCommaFiberIntervalIso G x y)).isQCatEquivalence
  exact (ht.comp he).ofFunctorIso (unitIntervalMap_commaTransportIso η x y).symm

/-- comma の始対象条件は、指定単位の各点の標準写像空間条件を与える。 -/
lemma unitMappingSpaceCondition_of_commaInitial
    (η : FunctorHom (𝟙 X) (F ≫ G)) (hη : UnitCommaInitialCondition η) :
    UnitMappingSpaceCondition η := by
  apply (unitMappingSpaceCondition_iff_interval η).mpr
  intro x y
  exact (unitIntervalMap_isQCatEquivalence_of_commaInitial η hη x y).isSimplicialHomotopyEquivalence

/-- 指定単位が comma の普遍矢印である条件は、標準写像空間の同値条件と同値。 -/
lemma unitCommaInitialCondition_iff_unitMappingSpaceCondition
    (η : FunctorHom (𝟙 X) (F ≫ G)) :
    UnitCommaInitialCondition η ↔ UnitMappingSpaceCondition η :=
  ⟨unitMappingSpaceCondition_of_commaInitial η,
    UnitMappingSpaceCondition.unitCommaInitialCondition⟩

/-- 元の指定単位を持つ随伴の存在は、その単位の comma 始対象条件と同値。 -/
lemma qcat_exists_adjunction_unitHom_iff_commaInitial
    (η : FunctorHom (𝟙 X) (F ≫ G)) :
    (∃ a : QCatAdjunction F G, a.unitHom = η) ↔ UnitCommaInitialCondition η :=
  (qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition η).trans
    (unitCommaInitialCondition_iff_unitMappingSpaceCondition η).symm

/-- 各始域の comma に始対象があれば、G は ∞ 右随伴。 -/
lemma exists_qcatAdjunction_of_commaFiberInitial (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (unitCommaFiber G x) _⦋0⦌, IsInitialVertex v) :
    ∃ F : X ⟶ Y, Nonempty (QCatAdjunction F G) := by
  obtain ⟨F, η, hη⟩ := exists_unit_initialCondition_of_fiberInitial G h
  exact ⟨F, ⟨qcatAdjunctionOfUnitMappingSpaceCondition η
    (unitMappingSpaceCondition_of_commaInitial η hη)⟩⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
