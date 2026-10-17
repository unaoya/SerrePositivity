module
public import SerrePositivity.DifferentialGraded.Complexes.ExactColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # 厳密な複体図式の exact な余極限による擬同型の保存

ホモトピー圏内だけで与えられた図式には、この補題を適用しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
  [Small.{u} J] [HasColimitsOfShape J (ModuleCat.{u} A)]
  [HasExactColimitsOfShape J (ModuleCat.{u} A)]

def complexTransposeMap {F G : J ⥤ Complex A} (α : F ⟶ G) :
    complexDiagramTranspose A F ⟶ complexDiagramTranspose A G where
  f i := Functor.whiskerRight α (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
  comm' i j _ := by
    apply NatTrans.ext
    funext k
    exact (α.app k).comm i j

omit [Small.{u} J] [HasColimitsOfShape J (ModuleCat.{u} A)]
  [HasExactColimitsOfShape J (ModuleCat.{u} A)] in
lemma complexTransposeMap_quasiIso {F G : J ⥤ Complex A} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (complexTransposeMap A α) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro j
  exact hα j

/-- 次数ごとの余極限で構成した複体と、指定された複体の余極限との同型。 -/
def complexColimitComparison (F : J ⥤ Complex A) :
    ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj
      (complexDiagramTranspose A F) ≅ colimit F :=
  (isColimitCoconeOfHasColimitEval F).coconePointUniqueUpToIso (colimit.isColimit F)

@[reassoc] lemma complexColimitComparison_ι (F : J ⥤ Complex A) (j : J) :
    (coconeOfHasColimitEval F).ι.app j ≫ (complexColimitComparison A F).hom = colimit.ι F j :=
  (isColimitCoconeOfHasColimitEval F).comp_coconePointUniqueUpToIso_hom _ j

lemma complexColimitComparison_naturality {F G : J ⥤ Complex A} (α : F ⟶ G) :
    (complexColimitComparison A F).hom ≫ colimMap α =
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α) ≫ (complexColimitComparison A G).hom := by
  apply (isColimitCoconeOfHasColimitEval F).hom_ext
  intro j
  rw [← Category.assoc, complexColimitComparison_ι, ι_colimMap, ← Category.assoc]
  have h : (coconeOfHasColimitEval F).ι.app j ≫
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α) = α.app j ≫ (coconeOfHasColimitEval G).ι.app j := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact ι_colimMap (Functor.whiskerRight α
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) j
  rw [h, Category.assoc, complexColimitComparison_ι]

/-- 対象ごと擬同型な厳密自然変換は、exact な余極限でも擬同型となる。 -/
lemma complex_colimMap_quasiIso {F G : J ⥤ Complex A} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colimMap α) := by
  have : (colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).Additive :=
    { map_add := by
        intro F G α β
        apply colimit.hom_ext
        intro j
        change colimit.ι F j ≫ colimMap (α + β) =
          colimit.ι F j ≫ (colimMap α + colimMap β)
        rw [ι_colimMap, Preadditive.comp_add, ι_colimMap, ι_colimMap]
        exact Preadditive.add_comp _ _ _ (α.app j) (β.app j) (colimit.ι G j) }
  have : QuasiIso (complexTransposeMap A α) := complexTransposeMap_quasiIso A α hα
  have : QuasiIso
      (((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α)) := inferInstance
  have he := complexColimitComparison_naturality A α
  have : QuasiIso ((complexColimitComparison A F).hom ≫ colimMap α) := by
    rw [he]
    infer_instance
  exact quasiIso_of_comp_left (complexColimitComparison A F).hom (colimMap α)

end SerrePositivity.DifferentialGraded.DGQuotient
