module
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveZero
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import SerrePositivity.InfinityCategories.DGNerve.TruncatedTriangles

/-! # dg 加群射と全 Hom 成分からの nerve の辺・三角形

概要：閉 dg 加群射を実際の辺へ、合成の差の原始元を二単体へ送る。
方針：Hom end の閉零成分を辺の比較へ渡し、各評価で合成を照合する。
規約：全次数の dg 自然性を保持する。使われ方：β3 の標準 cone 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D}

/-- 閉 dg 加群射を dg nerve の端点付きの辺へ送る。 -/
def dgModuleEdge (f : M ⟶ N) :
    (dgModuleNerve A D).Edge (Simplex.vertex (ForgetEnrichment.to (Complex A) M))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) N)) :=
  SSet.Edge.ofTruncated (edgeOfCycle (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)))

/-- 加群射の辺の閉零成分は元の Hom end の閉零成分。 -/
lemma dgModuleEdge_cycle (f : M ⟶ N) :
    edgeCycle (dgModuleEdge A D f).toTruncated =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f) := rfl

/-- 閉射の合成の次数零成分は全 Hom end 内の通常順合成。 -/
lemma dgModuleClosedCycle_comp (f : M ⟶ N) (g : N ⟶ P) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val =
      compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add 0) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π]
  have hf := moduleEvaluation_cochain A D x f
  have hg := moduleEvaluation_cochain A D x g
  have hfg := moduleEvaluation_cochain A D x (f ≫ g)
  rw [← hf, ← hg, ← hfg, CategoryTheory.Functor.map_comp, Cochain.ofHom_comp]

/-- 合成の差の原始元は実際の dg 加群の nerve の二単体を与える。 -/
def dgModuleCompStruct (f : M ⟶ N) (g : N ⟶ P) (h : M ⟶ P)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) h)).val) :
    SSet.Edge.CompStruct (dgModuleEdge A D f) (dgModuleEdge A D g) (dgModuleEdge A D h) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply compStructOfHomotopy _ _ _ t
  rw [dgModuleEdge_cycle, dgModuleEdge_cycle, dgModuleEdge_cycle]
  rw [← dgModuleClosedCycle_comp A D f g]
  exact ht

end SerrePositivity.InfinityCategories
