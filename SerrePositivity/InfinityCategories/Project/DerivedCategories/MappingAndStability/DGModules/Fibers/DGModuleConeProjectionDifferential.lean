module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveEdges
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # dg 加群の cone の第二射影の微分

概要：全 Hom end の第二射影の微分は第一射影と元の閉射の合成の負になる。
方針：各対象の評価で Mathlib の mapping cone の微分公式へ帰着する。
規約：通常順の合成を使う。使われ方：β3 の shifted cone の nullhomotopy。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- cone の第二射影の全 Hom end 内の微分公式。 -/
lemma dgModuleConeSndElement_d (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N)).d 0 1 (moduleConeSndElement A D f) =
      -compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
        (moduleConeFstElement A D f) (add_zero 1) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeSndElement_π, map_neg, moduleHomCompose_π,
    moduleConeFstElement_π]
  have hf := moduleEvaluation_cochain A D x f
  rw [← hf]
  exact mappingCone.δ_snd _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
