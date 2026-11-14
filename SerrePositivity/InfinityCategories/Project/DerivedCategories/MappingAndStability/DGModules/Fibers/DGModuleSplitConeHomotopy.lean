module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleSplitConeBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveHomotopyEquivalence
/-!
概要：閉分裂する右 dg 加群の cone 射影を全 dg 自然なホモトピー同値にする。
方針：同じ射影を cone の第二射影と第一包含の間に置いて収縮する。
規約：全 Hom end 内の原始元を明示する。
使われ方：元の閉射と二胞体を保つ分裂 cofiber 四角形の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Category Limits DifferentialGraded HomologicalComplex CochainComplex
  HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D}

def dgModuleSplitConeContractingElement (a : M ⟶ N) (r : N ⟶ M) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) (moduleCone A D a))).X (-1) :=
  -compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (compose A (x := ForgetEnrichment.to (Complex A) N)
      (y := ForgetEnrichment.to (Complex A) M)
      (z := ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (moduleConeInlElement A D a)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) r)).val (zero_add (-1)))
    (moduleConeSndElement A D a) (zero_add (-1))

lemma dgModuleSplitConeContractingElement_d
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hap : a ≫ p = 0) (hs : r ≫ a + p ≫ b = 𝟙 N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) (moduleCone A D a))).d (-1) 0
      (dgModuleSplitConeContractingElement A D a r) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeDesc A D a p hap ≫ b ≫ moduleConeInr A D a))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (𝟙 (moduleCone A D a)))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, dgModuleSplitConeContractingElement, map_neg,
    moduleHomCompose_π, moduleHomCompose_π, moduleConeInlElement_π,
    moduleConeSndElement_π, ← moduleEvaluation_cochain, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleConeDesc_eval, moduleConeInr_eval, CategoryTheory.Functor.map_id]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSplitCone_boundary
  · simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      congrArg (moduleEvaluation A D x).map har
  · have hh := congrArg (moduleEvaluation A D x).map hs
    change (moduleEvaluation A D x).map r ≫ (moduleEvaluation A D x).map a +
      (moduleEvaluation A D x).map p ≫ (moduleEvaluation A D x).map b = 𝟙 _
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_add,
      CategoryTheory.Functor.map_id] using hh

lemma dgModuleSplitConeDesc_homotopy_isIso
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hbp : b ≫ p = 𝟙 P) (hap : a ≫ p = 0)
    (hs : r ≫ a + p ≫ b = 𝟙 N) :
    IsIso ((moduleToHomotopy A D).map (moduleConeDesc A D a p hap)) := by
  let q := moduleConeDesc A D a p hap
  let g := b ≫ moduleConeInr A D a
  have hgq : g ≫ q = 𝟙 P := by
    dsimp only [g, q]
    rw [Category.assoc, moduleConeDesc_inr, hbp]
  let H : ModuleHomotopy A D (q ≫ g) (𝟙 _) := by
    refine ⟨dgModuleSplitConeContractingElement A D a r, ?_⟩
    dsimp only [q, g]
    exact dgModuleSplitConeContractingElement_d A D a r b p har hap hs
  have H' : ModuleHomotopy A D (g ≫ q) (𝟙 _) := by
    rw [hgq]
    exact ⟨0, by simp⟩
  change IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyIsoOfInverse A D q g H H').hom
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
