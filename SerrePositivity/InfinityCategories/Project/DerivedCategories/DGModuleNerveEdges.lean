module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveZero
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles

/-! # dg 加群射と全 Hom 成分からの nerve の辺・三角形

概要：閉 dg 加群射を実際の辺へ、合成の差の原始元を二単体へ送る。
方針：Hom end の閉零成分を辺の比較へ渡し、各評価で合成を照合する。
規約：全次数の dg 自然性を保持する。使われ方：β3 の標準 cone 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 閉 dg 加群射を dg nerve の端点付きの辺へ送る。 -/
def dgModuleEdge (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) M))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) N)) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)))

/-- 加群射の辺の閉零成分は元の Hom end の閉零成分。 -/
lemma dgModuleEdge_cycle (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (dgModuleEdge A D f).toTruncated =
      _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f) := rfl

/-- 閉射の合成の次数零成分は全 Hom end 内の通常順合成。 -/
lemma dgModuleClosedCycle_comp (f : M ⟶ N) (g : N ⟶ P) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (f ≫ g))).val =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) g)).val
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 0) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext A D
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  have hf := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain A D x f
  have hg := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain A D x g
  have hfg := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain A D x (f ≫ g)
  rw [← hf, ← hg, ← hfg, CategoryTheory.Functor.map_comp, Cochain.ofHom_comp]

/-- 合成の差の原始元は実際の dg 加群の nerve の二単体を与える。 -/
def dgModuleCompStruct (f : M ⟶ N) (g : N ⟶ P) (h : M ⟶ P)
    (t : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) P) (-1))
    (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) P)).d (-1) 0 t =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (f ≫ g))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) h)).val) :
    SSet.Edge.CompStruct (dgModuleEdge A D f) (dgModuleEdge A D g) (dgModuleEdge A D h) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStructOfHomotopy _ _ _ t
  rw [dgModuleEdge_cycle, dgModuleEdge_cycle, dgModuleEdge_cycle]
  rw [← dgModuleClosedCycle_comp A D f g]
  exact ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories
