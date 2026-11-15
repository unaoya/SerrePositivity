module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeInternalHomEvaluation

/-!
概要：同じ反転end同型のuncurryは元のuncurryの指定反転を返す。
方針：既存のend射影則と内部Homの反転評価則を合成する。
規約：IS-W2 B02の既存構成の合成・貼り合わせ。重み、パラメータ、全単体を保持する。
使われ方：HA 1.2.4、元の反転BK比較を指定豊穣合成へ輸送する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
variable {I : Type u} [SmallCategory I]

/-- 同じendの反転同型を通したuncurryの各成分。 -/
theorem weightedSectionsOppositeIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsOppositeIso W H).hom)).app i =
    (opTensorIso (W.obj i) S).hom ≫ SSet.opFunctor.map ((weightedSectionsUncurry f).app i) := by
  change uncurry ((SSet.opFunctor.map f ≫ (weightedSectionsOppositeIso W H).hom) ≫
    weightedSectionsπ (W ⋙ SSet.opFunctor) (H ⋙ SSet.opFunctor) i) = _
  rw [Category.assoc, weightedSectionsOppositeIso_π, ← Category.assoc,
    ← SSet.opFunctor.map_comp]
  exact oppositeInternalHom_map_uncurry (f ≫ weightedSectionsπ W H i)

/-- 元の重みに戻した反転endのuncurryは、同じ再反転と元のuncurryの反転。 -/
theorem weightedSectionsReflectedIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections (W ⋙ SSet.opFunctor) H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsReflectedIso W H).hom)).app i =
    ((diagramDoubleOppositeIso W).inv.app i ▷ S.op) ≫
      (opTensorIso ((W ⋙ SSet.opFunctor).obj i) S).hom ≫
        SSet.opFunctor.map ((weightedSectionsUncurry f).app i) := by
  dsimp only [weightedSectionsReflectedIso, Iso.trans_hom, weightedSectionsWeightIso]
  rw [← Category.assoc, weightedSectionsUncurry_comp_pre]
  change ((diagramDoubleOppositeIso W).inv.app i ▷ S.op) ≫
    (weightedSectionsUncurry (SSet.opFunctor.map f ≫
      (weightedSectionsOppositeIso (W ⋙ SSet.opFunctor) H).hom)).app i = _
  rw [weightedSectionsOppositeIso_uncurry]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
