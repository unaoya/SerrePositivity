module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberNullHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeDesc
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # dg 加群の標準 fiber から cofiber への実比較射

概要：cone(fiber(f)→M) から N への閉加群射を構成する。
方針：fiber の零ホモトピーと元の閉射 f を cone の二成分の降下へ渡す。
規約：標準包含と実ホモトピーを厳密に保持する。使われ方：β3 の双対の比較辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 fiber の射影の cone から元の標的への閉加群射。 -/
def dgModuleFiberCofiberDesc (f : M ⟶ N) :
    moduleCone A D (dgModuleFiberProjection A D f) ⟶ N :=
  moduleConeDescOfBoundary A D (dgModuleFiberProjection A D f)
    (dgModuleFiberNullHomotopy A D f) f (dgModuleFiberNullHomotopy_differential A D f)

/-- 降下比較の閉零成分は全 Hom end の二成分からの復元。 -/
lemma dgModuleFiberCofiberDesc_cycle (f : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleFiberCofiberDesc A D f))).val =
      dgModuleConeDescElement A D (dgModuleFiberProjection A D f) (-1)
        (dgModuleFiberNullHomotopy A D f)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val := by
  exact moduleMorphismOfCycle_cycle A D _ _

/-- 標準包含の後の降下比較は元の射 f。 -/
lemma dgModuleFiberCofiberDesc_inr (f : M ⟶ N) :
    moduleConeInr A D (dgModuleFiberProjection A D f) ≫ dgModuleFiberCofiberDesc A D f = f :=
  moduleConeDescOfBoundary_inr A D _ _ _ _

/-- 降下比較は fiber の実零ホモトピーを保持する。 -/
lemma dgModuleFiberCofiberDesc_inl (f : M ⟶ N) :
    compose A (cycleFromUnit _
      (ForgetEnrichment.homTo (Complex A) (dgModuleFiberCofiberDesc A D f))).val
      (moduleConeInlElement A D (dgModuleFiberProjection A D f)) (add_zero (-1)) =
        dgModuleFiberNullHomotopy A D f := by
  rw [dgModuleFiberCofiberDesc_cycle]
  exact dgModuleConeDescElement_inl A D (dgModuleFiberProjection A D f) (-1) _ _

end SerrePositivity.InfinityCategories
