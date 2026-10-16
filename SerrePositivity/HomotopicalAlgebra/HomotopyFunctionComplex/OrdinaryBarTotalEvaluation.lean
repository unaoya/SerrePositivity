module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftElements

/-! # The labelled total cone factors through the same small evaluation

The changing row is indexed by the actual simplex category of the small
reference output. The factorization preserves the entire simplex operator.
No weak equivalence of an evaluation or a category nerve is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev rowBase : (OrdinaryBarFirstAction.output R).Elements ⥤
    OrdinaryBarCenters.Comma R × SimplexCategoryᵒᵖ :=
  ((Functor.Elements.π (OrdinaryBarFirstAction.output R)) ⋙
    OrdinaryResolutionRows.commaRows R).prod'
      (Functor.Elements.π (OrdinaryBarFirstAction.output R))

lemma rowLabel_naturality {s t : (OrdinaryBarFirstAction.output R).Elements} (f : s ⟶ t) :
    ((rowBase R) ⋙ OrdinaryBarTotalCone.values R).map f s.val = t.val := by
  have h := (ResolutionRowMixedMapping.componentIso R).hom.naturality f.hom
  have hx := congrArg (fun k => k s.val) h
  exact hx.trans f.map_val

def rowLabels : (OrdinaryBarFirstAction.output R).Elements ⥤
    ((rowBase R) ⋙ OrdinaryBarTotalCone.values R).Elements where
  obj s := ((rowBase R) ⋙ OrdinaryBarTotalCone.values R).elementsMk s s.val
  map f := Functor.Elements.homMk f (rowLabel_naturality R f)

abbrev rowElements : (OrdinaryBarFirstAction.output R).Elements ⥤
    OrdinaryBarTotalCone.Total R :=
  rowLabels R ⋙ Functor.Elements.precomp (rowBase R) (OrdinaryBarTotalCone.values R)

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev evaluationElements : OrdinaryBarTotalCone.Index R ⥤
    (OrdinaryBarFirstAction.output R).Elements :=
  (OrdinaryBarEvaluation.evaluation R a b).mapElements ⋙
    UniverseLift.downElements (OrdinaryBarFirstAction.output R)

def rowFactorization : OrdinaryBarTotalCone.rows R a b ≅
    evaluationElements R a b ⋙ rowElements R :=
  NatIso.ofComponents (fun s => Functor.Elements.isoMk (Iso.refl _) (by
    change ((OrdinaryBarTotalCone.values R).map (𝟙 _))
      ((OrdinaryBarTotalCone.rows R a b).obj s).val =
        ((OrdinaryBarEvaluation.evaluation R a b).app s.obj s.val).down
    rw [CategoryTheory.Functor.map_id]
    exact OrdinaryBarTotalCone.row_label R a b s.obj s.val)) (by
      intro s t f
      apply Functor.Elements.hom_ext
      change (OrdinaryBarTotalCone.rowBase R).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (OrdinaryBarTotalCone.rowBase R).map f
      simp only [Category.comp_id, Category.id_comp])

abbrev comparison : OrdinaryBarTotalCone.first R ⟶
    evaluationElements R a b ⋙ rowElements R :=
  OrdinaryBarTotalCone.cone R a b ≫ (rowFactorization R a b).hom

lemma comparison_degree (s : OrdinaryBarTotalCone.Index R) :
    ((comparison R a b).app s).hom.2 = 𝟙 s.obj := by
  change 𝟙 s.obj ≫ 𝟙 s.obj = 𝟙 s.obj
  exact Category.id_comp _

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
