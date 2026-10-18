module

public import SerrePositivity.KST.Spectra.CochainDensityEquiv
public import SerrePositivity.KST.Spectra.TotalizationFibration

/-!
概要：Tot と完全な重みの end の Hom の同値のパラメーターへの自然性。
方針：標準単体上の族の右因子の前合成と二つの end の uncurry を比較する。
規約：実際の通常の射の等式を示す。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Yoneda による模型の同型の構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories.HomotopyLimits

namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {W H : I ⥤ SSet.{u}} {A B : SSet.{u}}

/-- 概要：図式上の密度の族のパラメーターを前合成する。
方針：各対象の族に同じ射を前合成する。
規約：添字と単体次数の二つの自然性を保つ。
使われ方：Goerss–Jardine VIII §1。密度による Hom の同値の自然性。 -/
def DiagramFamily.preParameter (s : DiagramFamily W H B) (f : A ⟶ B) :
    DiagramFamily W H A where
  app i := (s.app i).preParameter f
  naturality {i j} g := by
    apply Family.ext
    intro n
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    have h := congrArg (fun t ↦ t.app n) (s.naturality g)
    exact congr($(NatTrans.congr_app h k) (x.1, (x.2.1, f.app k x.2.2)))

lemma diagramDiagonal_preParameter (s : DiagramFamily W H B) (f : A ⟶ B) :
    diagramDiagonal (s.preParameter f) =
      (W ◁ (Functor.const I).map f) ≫ diagramDiagonal s := by
  apply NatTrans.ext
  funext i
  exact diagonal_preParameter (s.app i) f

lemma fromCochains_preParameter
    (s : SimplexTensorBoundary.diagram B ⟶
      UnderlyingWeightedCochains.obj (discreteLevels W) H) (f : A ⟶ B) :
    fromCochains (SimplexTensorBoundary.map f ≫ s) = (fromCochains s).preParameter f := by
  apply DiagramFamily.ext
  intro i
  apply Family.ext
  intro n
  change (weightedSectionsUncurry ((SSet.stdSimplex.obj n ◁ f) ≫ s.app n)).app i = _
  rw [weightedSectionsUncurry_precomp]
  rfl

/-- 概要：通常の Tot と重みの end の Hom の同値はパラメーターへの前合成と可換。
方針：uncurry、族の交換、対角評価、end の持ち上げの各前合成の式を使う。
規約：Kan 条件を持たない通常の射の等式。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。Yoneda の完全忠実性への入力。 -/
lemma totalizationEndHomEquiv_pre (W H : I ⥤ SSet.{u}) (f : A ⟶ B)
    (s : B ⟶ CosimplicialTotalization.obj
      (UnderlyingWeightedCochains.obj (discreteLevels W) H)) :
    totalizationEndHomEquiv W H A (f ≫ s) = f ≫ totalizationEndHomEquiv W H B s := by
  change weightedSectionsLift (diagramDiagonal
      (fromCochains (CosimplicialTotalization.uncurry (f ≫ s)))) =
    f ≫ weightedSectionsLift (diagramDiagonal
      (fromCochains (CosimplicialTotalization.uncurry s)))
  rw [CosimplicialTotalization.uncurry_pre, fromCochains_preParameter,
    diagramDiagonal_preParameter]
  apply (weightedSectionsHomEquiv W H A).injective
  change weightedSectionsUncurry (weightedSectionsLift _) = weightedSectionsUncurry (_ ≫ _)
  rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift,
    weightedSectionsUncurry_lift]

end

end SerrePositivity.KST.Spectra.SimplexDensity
