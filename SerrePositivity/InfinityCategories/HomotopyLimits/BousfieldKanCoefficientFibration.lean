module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedNerveTrivialFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsLifting
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsDiagramNaturality

/-!
概要：Bousfield–Kan end は係数の成分ごとの自明 Kan fibration を保つ。
方針：weighted nerve とその切断空間の持ち上げ性を、既存の自然同型で end へ移す。
規約：図式の遷移の fibration 性や値の Kan 性を要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の homotopy 極限の係数に関する同値不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan end の係数写像は切断空間の係数写像を標準同型で共役した射。
方針：切断空間との同型の自然性に逆同型を後合成する。
規約：係数図式と自然変換は任意。
使われ方：Kerodon 7.5.3.12 の持ち上げ性を end の実際の射へ移す等式。 -/
lemma bousfieldKanMap_eq_sections {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedSectionsMap (bousfieldKanWeight I) η =
      (bousfieldKanSectionsIso F).hom ≫
        simplicialSectionsMap (weightedNerveMap η) (weightedNerveMap_projection η) ≫
          (bousfieldKanSectionsIso G).inv := by
  have h := congrArg (fun q ↦ q ≫ (bousfieldKanSectionsIso G).inv)
    (bousfieldKanSectionsMap_naturality η)
  change ((bousfieldKanSectionsIso F).hom ≫
      simplicialSectionsMap (weightedNerveMap η) (weightedNerveMap_projection η)) ≫
        (bousfieldKanSectionsIso G).inv =
    (weightedSectionsMap (bousfieldKanWeight I) η ≫ (bousfieldKanSectionsIso G).hom) ≫
      (bousfieldKanSectionsIso G).inv at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

/-- 概要：係数の成分ごとの自明 Kan fibration は Bousfield–Kan end でも自明 Kan fibration。
方針：weighted nerve の全空間と切断空間の持ち上げ性を自然同型で移す。
規約：値の Kan 性も遷移の fibration 性も要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の end の係数に関する比較。 -/
lemma bousfieldKanMap_trivialKanFibration {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    [∀ i, TrivialKanFibration (η.app i)] :
    TrivialKanFibration (weightedSectionsMap (bousfieldKanWeight I) η) := by
  have h := simplicialSectionsMap_trivialKanFibration (weightedNerveMap η)
    (weightedNerveMap_projection η)
  rw [bousfieldKanMap_eq_sections]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (MorphismProperty.rlp_of_isIso _ _)
    (trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _))⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
