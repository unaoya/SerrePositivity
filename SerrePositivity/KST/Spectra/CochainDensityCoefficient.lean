module

public import SerrePositivity.KST.Spectra.CochainDensityIso
public import SerrePositivity.KST.Spectra.UnderlyingWeightedCochainMap
public import SerrePositivity.KST.Spectra.FreeActionEndNaturality

/-!
概要：通常の Tot と完全な重みの end の密度の同型の係数への自然性。
方針：族の係数の後合成、二添字の交換、対角評価の各式を比較する。
規約：Kan 条件を使わず通常の単体集合の射の等式を示す。
使われ方：Goerss–Jardine VIII §§1–2。hG と Tot の係数の射の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {W H E : I ⥤ SSet.{u}} {A : SSet.{u}}

/-- 概要：図式上の密度の族を係数の自然変換で後合成する。
方針：各対象の族を後合成し、係数と族の二つの自然性を使う。
規約：重みとパラメーターは固定する。
使われ方：Goerss–Jardine VIII §1。Hom の密度の同値の係数への自然性。 -/
def DiagramFamily.postCoefficient (s : DiagramFamily W H A) (τ : H ⟶ E) :
    DiagramFamily W E A where
  app i := (s.app i).postCoefficient (τ.app i)
  naturality {i j} g := by
    apply Family.ext
    intro n
    have h := congrArg (fun t ↦ t.app n) (s.naturality g)
    change ((Functor.const (SimplexCategoryᵒᵖ)).map ((W.map g).app (Opposite.op n)) ▷
        (SSet.stdSimplex.obj n ⊗ A)) ≫ (s.app j).app n = (s.app i).app n ≫ H.map g at h
    change ((Functor.const (SimplexCategoryᵒᵖ)).map ((W.map g).app (Opposite.op n)) ▷
        (SSet.stdSimplex.obj n ⊗ A)) ≫ ((s.app j).app n ≫ τ.app j) =
      ((s.app i).app n ≫ τ.app i) ≫ E.map g
    rw [← Category.assoc, h, Category.assoc, τ.naturality g, ← Category.assoc]

lemma diagramDiagonal_postCoefficient (s : DiagramFamily W H A) (τ : H ⟶ E) :
    diagramDiagonal (s.postCoefficient τ) = diagramDiagonal s ≫ τ := by
  apply NatTrans.ext
  funext i
  exact diagonal_postCoefficient (s.app i) (τ.app i)

lemma fromCochains_postCoefficient (s : SimplexTensorBoundary.diagram A ⟶
    UnderlyingWeightedCochains.obj (discreteLevels W) H) (τ : H ⟶ E) :
    fromCochains (s ≫ UnderlyingWeightedCochains.map (discreteLevels W) τ) =
      (fromCochains s).postCoefficient τ := by
  apply DiagramFamily.ext
  intro i
  apply Family.ext
  intro n
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (s.app n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _ τ)).app i = _
  rw [FreeActionFamily.sectionsUncurry_post]
  rfl

lemma totalizationEndHomEquiv_post (W : I ⥤ SSet.{u}) {H E : I ⥤ SSet.{u}} (τ : H ⟶ E)
    (s : A ⟶ CosimplicialTotalization.obj
      (UnderlyingWeightedCochains.obj (discreteLevels W) H)) :
    totalizationEndHomEquiv W E A
        (s ≫ CosimplicialTotalization.map (UnderlyingWeightedCochains.map (discreteLevels W) τ)) =
      totalizationEndHomEquiv W H A s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W τ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (diagramDiagonal (fromCochains
      (CosimplicialTotalization.uncurry (s ≫ CosimplicialTotalization.map _)))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (diagramDiagonal (fromCochains (CosimplicialTotalization.uncurry s))) ≫ _
  rw [CosimplicialTotalization.uncurry_map, fromCochains_postCoefficient,
    diagramDiagonal_postCoefficient, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_postcomp]

/-- 概要：通常の Tot と完全な重みの end の密度の同型は係数の射に自然。
方針：Hom の同値の係数への自然性を恒等射に適用する。
規約：実際の比較同型の順射の可換式。
使われ方：Goerss–Jardine VIII §§1–2。Tot と hG の関手的な模型比較。 -/
lemma totalizationEndIso_natural (W : I ⥤ SSet.{u}) {H E : I ⥤ SSet.{u}} (τ : H ⟶ E) :
    CosimplicialTotalization.map (UnderlyingWeightedCochains.map (discreteLevels W) τ) ≫
        (totalizationEndIso W E).hom =
      (totalizationEndIso W H).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W τ := by
  rw [← totalizationEndHomEquiv_apply, totalizationEndIso_hom]
  simpa only [Category.id_comp] using totalizationEndHomEquiv_post W τ (𝟙 _)

end

end SerrePositivity.KST.Spectra.SimplexDensity
