module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveEdges

/-! # 閉加群射と全 Hom end の成分の照合

概要：閉加群射の等号を次数零成分の等号から回収する。
方針：閉射と零サイクルの同値の単射性を使う。
規約：恒等成分は dg 単位。使われ方：β3 の標準比較射の厳密な合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom end の閉零成分の一致から閉加群射の一致を得る。 -/
lemma dgModuleMorphism_ext_cycle {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val) : f = g := by
  apply (closedHomEquiv A (RightModule A D) M N).injective
  exact Subtype.ext h

/-- 恒等加群射の閉零成分は全 Hom end の dg 単位。 -/
lemma dgModuleClosedCycle_id (M : ModuleCategory A D) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (𝟙 M))).val =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
