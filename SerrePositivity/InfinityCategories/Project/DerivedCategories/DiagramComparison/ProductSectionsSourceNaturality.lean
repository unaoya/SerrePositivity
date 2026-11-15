module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedAdjunctionSourceNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeFrameWeightMaps
/-!
概要：元の自由積Hom同型は重みの全射に自然。
方針：同じ合成随伴の重み自然性と標準単体Hom同型の標的自然性を合成する。
規約：A11の同じ前提計算2/3の証明分割。元の二同型を使用する。
使われ方：HA 1.2.4、指定正規化重み比較の前合成自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
/-- 指定自由積Hom同型は元の重みの全射と可換。 -/
theorem freeProductSectionsHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    (cosimplicialHomMap (freeProductFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeProductSectionsHomIso A W' Q).hom =
    (freeProductSectionsHomIso A W Q).hom ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) := by
  let S := SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0}
  let H := Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A
  let e := (adjunctionHomIsoSameUniverse
    ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)) S).app Q
  let e' := (adjunctionHomIsoSameUniverse
    ((weightedSectionsAdjunction W').comp (freeNegativeChainsDiagramAdjunction A J)) S).app Q
  let r := weightedSectionsPre w H
  have hi : (cosimplicialHomMap
      (freeProductFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫ e'.hom =
      e.hom ≫ (cosimplicialHom S).map r := by
    ext n s
    change ((weightedSectionsAdjunction W').comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
      (S.obj n.unop) Q
      ((freeNegativeChainsDiagramFunctor A J).map (w ▷ (Functor.const J).obj (S.obj n.unop)) ≫ s) =
      ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
        (S.obj n.unop) Q s ≫ r
    exact freeWeightedAdjunction_weight_naturality A w (S.obj n.unop) Q s
  have hl := liftedStandardSimplexHomIso_naturality r
  have h1 := congrArg (fun z => z ≫ (liftedStandardSimplexHomIso (weightedSections W' H)).hom) hi
  have h2 := congrArg (fun z => e.hom ≫ z) hl
  simp only [Category.assoc] at h1 h2
  simpa only [freeProductSectionsHomIso, Iso.trans_hom, Functor.comp_obj,
    weightedSectionsFunctor, Functor.whiskeringRight, Category.assoc] using h1.trans h2
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
