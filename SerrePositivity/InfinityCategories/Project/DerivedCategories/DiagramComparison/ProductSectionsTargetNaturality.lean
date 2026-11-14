module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsHom
/-!
概要：元の自由積Homと重み付き切断の同型の標的自然性。
方針：元の合成随伴Hom同型と持ち上げ標準単体Hom同型の自然性を使う。
規約：A10の前提計算2/3。同じ自然同型の成分を保持する。
使われ方：HA 1.2.4、指定正規化重み比較の全図式射自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 同じ持ち上げ標準単体Hom同型の標的自然性。 -/
theorem liftedStandardSimplexHomIso_naturality {Z Z' : SSet.{u}} (f : Z ⟶ Z') :
    (cosimplicialHom (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})).map f ≫
      (liftedStandardSimplexHomIso Z').hom = (liftedStandardSimplexHomIso Z).hom ≫ f := by
  let e : cosimplicialHom (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0}) ≅ 𝟭 SSet.{u} :=
    (cosimplicialHomBifunctor.mapIso liftedStandardSimplexIso.op).symm ≪≫
      SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.homIso
  exact e.hom.naturality f
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
/-- 指定自由積Hom同型は標的の全図式射と可換。 -/
theorem freeProductSectionsHomIso_target_naturality (W : J ⥤ SSet.{u})
    {Q Q' : J ⥤ CochainComplex (ModuleCat A) ℤ} (f : Q ⟶ Q') :
    (cosimplicialHom (freeProductFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeProductSectionsHomIso A W Q').hom =
    (freeProductSectionsHomIso A W Q).hom ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (CochainComplex (ModuleCat A) ℤ) SSet.{u}).obj
        (SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) |>.map f) := by
  let e := adjunctionHomIsoSameUniverse
    ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J))
    (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})
  change _ ≫ (e.hom.app Q' ≫ (liftedStandardSimplexHomIso _).hom) =
    (e.hom.app Q ≫ (liftedStandardSimplexHomIso _).hom) ≫ _
  rw [← Category.assoc]
  erw [e.hom.naturality]
  rw [Category.assoc]
  have hl := liftedStandardSimplexHomIso_naturality
    ((weightedSectionsFunctor W).map
      (((Functor.whiskeringRight J (CochainComplex (ModuleCat A) ℤ) SSet.{u}).obj
        (SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A)).map f))
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using congrArg (fun z => e.hom.app Q ≫ z) hl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
