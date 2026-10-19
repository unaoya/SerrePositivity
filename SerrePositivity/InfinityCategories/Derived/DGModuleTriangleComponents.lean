module
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveEdges
public import SerrePositivity.InfinityCategories.DGNerve.TripleHom

/-! # dg 加群の実合成三角形の全成分

概要：実際の二単体の三辺とホモトピーを元の Hom end の成分と同定する。
方針：合成三角形の構成を評価する。規約：次数 −1 の符号を変えない。
使われ方：β3 の cone の境界残差に標準四角形の成分を代入する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D}
variable (f : M ⟶ N) (g : N ⟶ P) (h : M ⟶ P)
variable (t : GradedHom A (ForgetEnrichment.to (Complex A) M)
  (ForgetEnrichment.to (Complex A) P) (-1))
variable (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
  (ForgetEnrichment.to (Complex A) P)).d (-1) 0 t =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val -
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) h)).val)

/-- 加群の合成三角形の対象族は指定された三対象。 -/
lemma dgModuleCompStruct_obj (i : Fin 3) :
    (dgModuleCompStruct A D f g h t ht).simplex.obj i =
      HomotopyComparison.tripleObj (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) i := rfl

/-- 最初の辺の成分は最初の閉加群射の成分。 -/
lemma dgModuleCompStruct_edge01 :
    (dgModuleCompStruct A D f g h t ht).simplex.toSimplexData.edgeHom 0 1 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val := rfl

/-- 最後の辺の成分は二番目の閉加群射の成分。 -/
lemma dgModuleCompStruct_edge12 :
    (dgModuleCompStruct A D f g h t ht).simplex.toSimplexData.edgeHom 1 2 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val := rfl

/-- 対角の成分は指定された対角の閉加群射の成分。 -/
lemma dgModuleCompStruct_edge02 :
    (dgModuleCompStruct A D f g h t ht).simplex.toSimplexData.edgeHom 0 2 (by decide) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) h)).val := rfl

/-- 三点の高次成分は指定された Hom end の原始元。 -/
lemma dgModuleCompStruct_triple :
    (dgModuleCompStruct A D f g h t ht).simplex.toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = t := rfl

end SerrePositivity.InfinityCategories
