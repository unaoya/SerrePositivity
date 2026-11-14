module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarDegreeNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalHomValues

/-!
概要：指定比較同型によるbarの関手が、各次数で元のラベルごとの自然変換そのものを写すと示す。
方針：元の次数別余積の脚で判定し、同じ全複体比較を後合成して相殺する。
規約：異なるbarの作用を仮定で同一視しない。元の列の自然性を使用する。
使われ方：3b-3 R6、MC微分と正規化射影の自然性へつなぐ同じ成分の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- MC微分を入れた同じbarの射も、各内部次数では元のgraded直和の射そのもの。 -/
lemma strictBarUnnormalizedMap_component
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) (q : ℤ) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η)).f q =
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarGradedMap A J η)).f q := by
  apply (smallStrictBarSourceDegreeCofan_isColimit A F q).hom_ext
  rintro ⟨s⟩
  let iF := ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)).f q
  let iG := ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A G)) s)).f q
  let a := (smallStrictBarTotalPointIso A F).hom.f q
  let b := (smallStrictBarTotalPointIso A G).hom.f q
  let v := ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    ((moduleShiftFunctor A PUnit.{1} (s.1 : ℤ)).map (η.app (s.2.down.obj 0)))).f q
  have hF : iF ≫ a = (smallStrictBarDegreeCofan A F q).inj s := by
    dsimp only [iF, a]
    rw [smallStrictBarTotalPointIso_hom]
    exact smallStrictBarTotalHom_point_ι A F q s
  have hG : iG ≫ b = (smallStrictBarDegreeCofan A G q).inj s := by
    dsimp only [iG, b]
    rw [smallStrictBarTotalPointIso_hom]
    exact smallStrictBarTotalHom_point_ι A G q s
  have hc : (moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η) ≫
      (smallStrictBarTotalPointIso A G).hom =
    (smallStrictBarTotalPointIso A F).hom ≫ (strictBarTotalComplexFunctor A J).map η :=
      (strictBarUnnormalizedTotalIso A J).hom.naturality η
  have hcq := congrArg (fun f => f.f q) hc
  simp only [HomologicalComplex.comp_f] at hcq
  have hg : iF ≫ ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      (strictBarGradedMap A J η)).f q = v ≫ iG := by
    have h := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q)
      (strictBarGradedMap_ι A J η s)
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using! h
  haveI : IsIso b := by
    change IsIso (((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q).mapIso
      (smallStrictBarTotalPointIso A G)).hom)
    infer_instance
  apply (cancel_mono b).mp
  change (iF ≫ _) ≫ b = (iF ≫ _) ≫ b
  calc
    _ = (smallStrictBarDegreeCofan A F q).inj s ≫
        ((strictBarTotalComplexFunctor A J).map η).f q := by
      rw [Category.assoc, hcq, ← Category.assoc, hF]
    _ = v ≫ (smallStrictBarDegreeCofan A G q).inj s :=
      smallStrictBarDegreeCofan_naturality A J η q s
    _ = _ := by rw [hg, Category.assoc, hG]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
