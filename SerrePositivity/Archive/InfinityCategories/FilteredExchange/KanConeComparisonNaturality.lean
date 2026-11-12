module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeFirstTetrahedronRelation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeLastTetrahedronRelation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PrismIsoCancellation

/-!
概要：Kan 錐の全円柱から得る脚の指定比較と元の錐の三角形の整合式。
方針：三つの比較三単体の合成則から共有面の二つの内部同型を消去する。
規約：元の頂点比較・図式成分・指定同型の値を保持。使われ方：filtered 引き戻し交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (K L : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K) (hd : d.vertex = coherentNerveVertex L)
  (a : K ⟶ L) (ha : (coneHomotopyApexEdge T).edge = (coherentNerveEdge a).edge)

/-- 概要：同じ円柱の上下三角形による各脚の指定比較。
方針：共通対角を消去。規約：別の同型を選ばない。使われ方：図式射に沿う整合式。 -/
def kanConeLegComparisonIso (i : I) :
    FunctorIso (kanNativeConeLeg c K hc i ≫ kanConeDiagramComponent T i)
      (a ≫ kanNativeConeLeg d L hd i) :=
  (kanConeLowerIso T K hc i).symm ≪≫ kanConeUpperIso T K L hc hd a ha i

/-- 概要：各脚の指定比較は元と比較先の錐の三角形・図式の比較に対して整合する。
方針：三つの四面の合成則から二つの内部同型を同時に消去。
規約：指定された値の合成の等式。使われ方：元の path の二次の整合性。 -/
lemma kanConeLegComparisonIso_naturality {i j : I} (f : i ⟶ j) :
    (kanNativeConeTriangleIso c K hc f).postcomp (kanConeDiagramComponent T j) ≪≫
      (kanConeDiagramComparisonIso T f).precomp
        (show K.obj ⟶ (F.obj i).obj from kanNativeConeLeg c K hc i) ≪≫
      (kanConeLegComparisonIso T K L hc hd a ha i).postcomp (G.map f) =
    kanConeLegComparisonIso T K L hc hd a ha j ≪≫
      (kanNativeConeTriangleIso d L hd f).precomp (show K.obj ⟶ L.obj from a) := by
  have h := prismIso_cancel
    (kanConeUpperIso T K L hc hd a ha j)
    ((kanNativeConeTriangleIso d L hd f).precomp (show K.obj ⟶ L.obj from a))
    (kanConeFirstInteriorIso T K hc f)
    ((kanConeUpperIso T K L hc hd a ha i).postcomp (G.map f))
    (kanConeSecondInteriorIso T K hc f)
    ((kanConeDiagramUpperIso T f).precomp
      (show K.obj ⟶ (F.obj i).obj from kanNativeConeLeg c K hc i))
    ((kanConeLowerIso T K hc i).postcomp (G.map f))
    ((kanConeDiagramLowerIso T f).precomp
      (show K.obj ⟶ (F.obj i).obj from kanNativeConeLeg c K hc i))
    (kanConeLowerIso T K hc j)
    ((kanNativeConeTriangleIso c K hc f).postcomp (kanConeDiagramComponent T j))
    (kanConeFirstTetrahedron_relation T K L hc hd a ha f)
    (kanConeMiddleTetrahedron_relation T K hc f) (kanConeLastTetrahedron_relation T K hc f)
  simpa only [kanConeDiagramComparisonIso, kanConeLegComparisonIso,
    functorIso_precomp_trans, functorIso_precomp_symm,
    functorIso_postcomp_trans, functorIso_postcomp_symm, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
