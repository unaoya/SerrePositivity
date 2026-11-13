module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedTensorHomSourceNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsSourceNaturality
/-!
概要：元の指定正規化重み比較は重みの全図式射に自然。
方針：同じ二つのHom同型と指定AWの重み自然性を合成する。
規約：IS-W2 A11。元の自由鎖の前合成と元の切断制限を使用する。
使われ方：HA 1.2.4、G10の標準重みの反転と持ち上げへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
/-- 同じ指定比較は重みの全射について元のΓ前合成と元の切断制限に整合する。 -/
theorem normalizedWeightSectionMap_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) :
    (truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q) ≫
        normalizedWeightSectionMap A W' Q φ =
    normalizedWeightSectionMap A W Q φ ≫ weightedSectionsPre w (Q ⋙ truncatedDoldKanFunctor A) := by
  let P := liftedStandardSimplexParameter J
  let e := freeTensorDiagramHomIso.{u,u} A Q W
  let e' := freeTensorDiagramHomIso.{u,u} A Q W'
  let a := (freeProductHomComparison A W P φ).app Q
  let a' := (freeProductHomComparison A W' P φ).app Q
  let t := (cosimplicialHomMap (freeTensorFrameWeightMap A w P)).app Q
  let p := (cosimplicialHomMap (freeProductFrameWeightMap A w P)).app Q
  let b := (freeProductSectionsHomIso A W Q).hom
  let b' := (freeProductSectionsHomIso A W' Q).hom
  let Hpre := (truncatedDoldKanFunctor A).map
    (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q)
  have hi : Hpre ≫ e'.inv = e.inv ≫ t := by
    have ht : t ≫ e'.hom = e.hom ≫ Hpre := freeTensorDiagramHomIso_weight_naturality A w Q
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, Iso.inv_hom_id_assoc]
  have hc : t ≫ a' = a ≫ p := by
    ext n g
    have hw := NatTrans.congr_app (freeProductFrameAW_weight_naturality A w P φ) n.unop
    change (freeProductFrameAW A W' P φ).app n.unop ≫
      ((freeTensorFrameWeightMap A w P).app n.unop ≫ g) =
        (freeProductFrameWeightMap A w P).app n.unop ≫
          ((freeProductFrameAW A W P φ).app n.unop ≫ g)
    simpa only [NatTrans.comp_app, Category.assoc] using congrArg (fun z => z ≫ g) hw.symm
  have hp := freeProductSectionsHomIso_weight_naturality A w Q
  have h1 := congrArg (fun z => z ≫ a' ≫ b') hi
  have h2 := congrArg (fun z => e.inv ≫ z ≫ b') hc
  have h3 := congrArg (fun z => e.inv ≫ a ≫ z) hp
  simp only [Category.assoc] at h1 h2 h3
  simpa only [normalizedWeightSectionMap, Category.assoc] using h1.trans (h2.trans h3)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
