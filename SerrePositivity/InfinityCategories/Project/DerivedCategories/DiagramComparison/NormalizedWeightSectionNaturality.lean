module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedTensorHomTargetNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsTargetNaturality
/-!
概要：元の指定正規化重み比較は標的の全図式射に自然。
方針：両側の同じHom同型の自然性と指定AW比較の自然性を合成する。
規約：IS-W2 A10。Γの元の図式Hom射と重み付き切断の元の射を使用する。
使われ方：HA 1.2.4、G10の指定錐と全図式射の族。
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
variable (W : J ⥤ SSet.{u}) (φ : simplicialRingCoefficient.{u} →+* A)
/-- 指定比較は標的の全図式射について同じΓ射・切断射と可換。 -/
theorem normalizedWeightSectionMap_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f) ≫
        normalizedWeightSectionMap A W Q' φ =
    normalizedWeightSectionMap A W Q φ ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (Complex A) SSet.{u}).obj (truncatedDoldKanFunctor A) |>.map f) := by
  let T := freeTensorFrame A W (liftedStandardSimplexParameter J)
  let P := freeProductFrame A W (liftedStandardSimplexParameter J)
  let e := freeTensorDiagramHomIso.{u,u} A Q W
  let e' := freeTensorDiagramHomIso.{u,u} A Q' W
  let a := freeProductHomComparison A W (liftedStandardSimplexParameter J) φ
  let p := freeProductSectionsHomIso A W Q
  let p' := freeProductSectionsHomIso A W Q'
  let Hmap := (truncatedDoldKanFunctor A).map
    (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f)
  have hi : Hmap ≫ e'.inv = e.inv ≫ (cosimplicialHom T).map f := by
    have ht : (cosimplicialHom T).map f ≫ e'.hom = e.hom ≫ Hmap :=
      freeTensorDiagramHomIso_target_naturality A W f
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, Iso.inv_hom_id_assoc]
  have hc : (cosimplicialHom T).map f ≫ a.app Q' = a.app Q ≫ (cosimplicialHom P).map f :=
    a.naturality f
  have hp := freeProductSectionsHomIso_target_naturality A W f
  have h1 := congrArg (fun z => z ≫ a.app Q' ≫ p'.hom) hi
  have h2 := congrArg (fun z => e.inv ≫ z ≫ p'.hom) hc
  have h3 := congrArg (fun z => e.inv ≫ a.app Q ≫ z) hp
  simp only [Category.assoc] at h1 h2 h3
  simpa only [normalizedWeightSectionMap, Category.assoc] using h1.trans (h2.trans h3)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
