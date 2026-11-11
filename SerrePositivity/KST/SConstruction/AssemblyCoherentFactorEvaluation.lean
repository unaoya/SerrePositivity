module
public import SerrePositivity.KST.SConstruction.AssemblyCoherentFactorSelections
public import SerrePositivity.KST.SConstruction.PointedArrowEvaluation
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedFamily

/-! # Coherent な両因子の元の写像族への評価
概要：全入力射列の選択を元の混合延長・逆射の写像空間へ自然に評価する。
方針：全選択の over 圏の族と図式の評価自然変換を合成する。
規約：全次数の射の等号で既存の二つの混合族を回収する。
使われ方：両因子の高次選択から構造射の自然性と列の厳密化へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Coherent な全延長選択を、元の点つき射の両側合成の図式へ評価する。 -/
def kanAssemblyCoherentEvaluation {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AssemblyInputArrow I) ⟶
      pointedMappingArrowDiagram (F ⋙ oneDirectionKanRealizationFunctor r)
        (F ⋙ loopBoundaryKanFunctor (r + 1)) :=
  kanAssemblyCoherentFamily r F v ≫ pointedExtensionArrowEvaluation
    (Functor.whiskerLeft F (oneDirectionKanUnitNat r))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r))

/-- Coherent な全逆射選択を、元の点つき射の両側合成の図式へ評価する。 -/
def oneDirectionInverseCoherentEvaluation {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AssemblyInputArrow I) ⟶
      pointedMappingArrowDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (F ⋙ oneDirectionKanRealizationFunctor r) :=
  oneDirectionInverseCoherentFamily r F v ≫ pointedLiftArrowEvaluation
    (Functor.whiskerLeft F (oneDirectionMappingPathProjectionNat r))
    (Functor.whiskerLeft F (oneDirectionMappingPathRetractionNat r))

/-- 全選択の延長側の評価は、元の混合延長族を全次数で厳密に回収する。 -/
lemma kanAssemblyCoherentEvaluation_app {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌)
    (x : AssemblyInputArrow I) :
    (kanAssemblyCoherentEvaluation r F v).app x =
      (kanAssemblyCoherentFamily r F v).app x ≫
        kanAssemblyMixedFamily r (F.map (assemblyArrowHom x)) := rfl

/-- 全選択の逆射側の評価は、元の混合逆射族を全次数で厳密に回収する。 -/
lemma oneDirectionInverseCoherentEvaluation_app {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    (x : AssemblyInputArrow I) :
    (oneDirectionInverseCoherentEvaluation r F v).app x =
      (oneDirectionInverseCoherentFamily r F v).app x ≫
        oneDirectionInverseMixedFamily r (F.map (assemblyArrowHom x)) := rfl

end SerrePositivity.KST.SConstruction
