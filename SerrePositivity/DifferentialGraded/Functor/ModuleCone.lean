module
public import SerrePositivity.DifferentialGraded.Functor.ClosedComplex
public import SerrePositivity.DifferentialGraded.Module.ConeElements

/-! # dg加群の標準coneと複体値dg関手の比較射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- coneの次数−1包含を主dg関手で送ったcochain。 -/
def moduleConeImageInl (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    Cochain ((F.toComplexFunctor A).obj M) ((F.toComplexFunctor A).obj (moduleCone A D f)) (-1) :=
  (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1) (moduleConeInlElement A D f)

lemma moduleConeImageInl_d (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    δ (-1) 0 (moduleConeImageInl A D F f) =
      Cochain.ofHom ((F.toComplexFunctor A).map f ≫
        (F.toComplexFunctor A).map (moduleConeInr A D f)) := by
  have hd := map_d_cochain A F (q := 0) (moduleConeInlElement A D f)
  have he := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0 z)
    (moduleConeInlElement_d A D f)
  have hc := map_closedElement A F (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at hc
  exact hd.symm.trans (he.trans hc)

/-- 既存の複体coneからdg加群coneの像への標準比較射。 -/
def moduleConeImageComparison (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((F.toComplexFunctor A).map f) ⟶ (F.toComplexFunctor A).obj (moduleCone A D f) :=
  mappingCone.desc ((F.toComplexFunctor A).map f) (moduleConeImageInl A D F f)
    ((F.toComplexFunctor A).map (moduleConeInr A D f)) (moduleConeImageInl_d A D F f)

@[reassoc]
lemma moduleConeImageComparison_inr (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr ((F.toComplexFunctor A).map f) ≫ moduleConeImageComparison A D F f =
      (F.toComplexFunctor A).map (moduleConeInr A D f) :=
  mappingCone.inr_desc _ _ _ _

lemma moduleConeImageComparison_inl (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (mappingCone.inl ((F.toComplexFunctor A).map f)).comp
      (Cochain.ofHom (moduleConeImageComparison A D F f)) (add_zero (-1)) =
      moduleConeImageInl A D F f :=
  mappingCone.inl_desc _ _ _ _

end SerrePositivity.DifferentialGraded.DGFunctor
