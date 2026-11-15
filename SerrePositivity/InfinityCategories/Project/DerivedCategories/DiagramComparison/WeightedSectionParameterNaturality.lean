module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedConeEndPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedHomComparison

/-!
概要：指定weighted endのパラメータ作用は、元の切断からの前合成を保つ。
方針：既存uncurry則を全成分で評価し、普遍切断のパラメータ自然性を使う。
規約：IS-W2 B06の既存構成の自然性。重みと全パラメータを保持する。
使われ方：HA 1.2.4、元のweighted点を固定した豊穣Hom作用の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I]

/-- 同じendのパラメータ作用へ切断を前合成すると、その切断自身の同じパラメータ作用。 -/
theorem weightedSectionsParameterMap_precomp (W H H' : I ⥤ SSet.{u})
    {K B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H')
    (p : K ⟶ weightedSections W H) :
    (p ⊗ₘ 𝟙 B) ≫ weightedSectionsParameterMap W η =
      weightedSectionsLift (weightedSectionParameterTransform (weightedSectionsUncurry p) η) := by
  apply (weightedSectionsHomEquiv W H' (K ⊗ B)).injective
  change weightedSectionsUncurry _ = weightedSectionsUncurry _
  rw [weightedSectionsUncurry_precomp, weightedSectionsParameterMap_uncurry,
    weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext i
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨w, k, b⟩
  have hp := congrArg (fun a => a.app i)
    (weightedSectionsUncurry_precomp p (𝟙 (weightedSections W H)))
  simp only [Category.comp_id, NatTrans.comp_app] at hp
  have hv := congrArg (fun h => h.app n (w, k)) hp
  change ((weightedSectionsUncurry p).app i).app n (w, k) =
    ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app n (w, p.app n k) at hv
  change (η.app i).app n
      (((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app n
        (w, p.app n k), b) =
    (η.app i).app n (((weightedSectionsUncurry p).app i).app n (w, k), b)
  exact congrArg (fun v => (η.app i).app n (v, b)) hv.symm

/-- 同じweighted錐の点をend作用の第一因子に固定すると、元の豊穣Hom比較になる。 -/
theorem reflectedWeightedHomComparison_point_precomposition
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (z : C)
    (φ : bousfieldKanWeight I ⟶ simplicialHomDiagram F z ⋙ SSet.opFunctor) (x : C) :
    let p := weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)
    (p ⊗ₘ 𝟙 (SimplicialCategory.sHom x z).op) ≫ weightedConeEndPrecomposition F x z =
      snd (Δ[0] : SSet.{u}) (SimplicialCategory.sHom x z).op ≫
        reflectedWeightedHomComparison F z φ x := by
  dsimp only [weightedConeEndPrecomposition, reflectedWeightedHomComparison]
  rw [weightedSectionsParameterMap_precomp]
  apply (weightedSectionsHomEquiv (bousfieldKanWeight I)
    (simplicialHomDiagram F x ⋙ SSet.opFunctor)
    ((Δ[0] : SSet.{u}) ⊗ (SimplicialCategory.sHom x z).op)).injective
  change weightedSectionsUncurry _ = weightedSectionsUncurry _
  simp only [weightedSectionsUncurry_lift, weightedSectionsUncurry_precomp]
  apply NatTrans.ext
  funext i
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨w, a, α⟩
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
