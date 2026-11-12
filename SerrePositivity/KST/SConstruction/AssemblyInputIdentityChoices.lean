module
public import SerrePositivity.KST.SConstruction.AssemblyFactorArrowDiagrams
public import SerrePositivity.KST.SConstruction.PointedChoiceBaseIso
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedFamily
public import SerrePositivity.KST.SConstruction.InverseMixedFamilyTransport

/-! # 恒等入力射の混合選択と元の因子選択の比較
概要：恒等入力射の成分を、元の Kan 随伴射・比較逆射の選択空間へ戻す。
方針：関手の恒等保存による制限射の等号を使う。
規約：同型は全次数の写像族と各頂点の実際の射を厳密に保持する。
使われ方：coherent な全選択から元の構造射の対象ごとの選択を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 恒等入力射では延長する元の射は元の随伴射そのもの。 -/
lemma kanAssemblyInputIdentity_constraint {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (oneDirectionReducedRealizationFunctor r).map (F.map (𝟙 i)) ≫
      (kanTargetAssemblyAdjointNat r).app (F.obj i) =
    (kanTargetAssemblyAdjointNat r).app (F.obj i) := by
  rw [F.map_id, (oneDirectionReducedRealizationFunctor r).map_id, Category.id_comp]

/-- 恒等入力射では持ち上げの底の射は恒等射そのもの。 -/
lemma oneDirectionInverseInputIdentity_constraint {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (boundaryKanRealizationFunctor r).map (F.map (𝟙 i)) =
      𝟙 ((boundaryKanRealizationFunctor r).obj (F.obj i)) := by
  rw [F.map_id, (boundaryKanRealizationFunctor r).map_id]

/-- 恒等入力射の延長選択空間と、元の随伴射の選択空間の同型。 -/
def kanAssemblyInputIdentityChoicesIso {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (kanAssemblyInputArrowDiagram r F).obj (assemblyArrowMk (𝟙 i)) ≅
      kanAssemblyAdjointChoices r (F.obj i) :=
  pointedExtensionBaseIso (PointedKanReplacement.unit.app (oneDirectionReducedRealization r (F.obj i)))
    (kanAssemblyInputIdentity_constraint r F i)

/-- 恒等入力射の逆射選択空間と、元の比較逆射の選択空間の同型。 -/
def oneDirectionInverseInputIdentityChoicesIso {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (oneDirectionInverseInputArrowDiagram r F).obj (assemblyArrowMk (𝟙 i)) ≅
      oneDirectionKanInverseChoices r (F.obj i) :=
  pointedLiftBaseIso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app (F.obj i)))
    (oneDirectionInverseInputIdentity_constraint r F i)

/-- 恒等入力射の比較は元の随伴射の族を全次数で厳密に回収する。 -/
lemma kanAssemblyInputIdentityChoicesIso_family {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (kanAssemblyInputIdentityChoicesIso r F i).hom ≫ kanAssemblyAdjointFamily r (F.obj i) =
      kanAssemblyMixedFamily r (F.map (𝟙 i)) :=
  pointedExtensionBaseIso_projection
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r (F.obj i)))
    (kanAssemblyInputIdentity_constraint r F i)

/-- 恒等入力射の比較は元の逆射の族を全次数で厳密に回収する。 -/
lemma oneDirectionInverseInputIdentityChoicesIso_family {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (oneDirectionInverseInputIdentityChoicesIso r F i).hom ≫
        pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app (F.obj i)) =
      oneDirectionInverseMixedFamily r (F.map (𝟙 i)) :=
  pointedLiftBaseIso_evaluation
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app (F.obj i)))
    (oneDirectionInverseInputIdentity_constraint r F i)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app (F.obj i)))

/-- 恒等入力射の比較後に取り出す随伴射は元の混合選択の射そのもの。 -/
lemma kanAssemblyInputIdentityChoicesIso_map {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I)
    (v : ((kanAssemblyInputArrowDiagram r F).obj (assemblyArrowMk (𝟙 i))) _⦋0⦌) :
    kanAssemblyAdjointAt r (F.obj i)
        ((kanAssemblyInputIdentityChoicesIso r F i).hom.app (Opposite.op ⦋0⦌) v) =
      kanAssemblyMixedMap r (F.map (𝟙 i)) v := by
  apply (familyVertexEquiv ((oneDirectionKanRealizationFunctor r).obj (F.obj i))
    ((loopBoundaryKanFunctor (r + 1)).obj (F.obj i))).injective
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (kanAssemblyInputIdentityChoicesIso_family r F i) (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  have hv : (kanAssemblyMixedFamily r (F.map (𝟙 i))).app (Opposite.op ⦋0⦌) v =
      familyVertex (kanAssemblyMixedMap r (F.map (𝟙 i)) v) :=
    (familyVertex_familyMap _ _ _).symm
  exact (kanAssemblyAdjointFamily_vertex r (F.obj i) _).symm.trans (h.trans hv)

/-- 恒等入力射の比較後に取り出す逆射は元の混合選択の射そのもの。 -/
lemma oneDirectionInverseInputIdentityChoicesIso_map {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I)
    (v : ((oneDirectionInverseInputArrowDiagram r F).obj (assemblyArrowMk (𝟙 i))) _⦋0⦌) :
    oneDirectionKanInverseAt r (F.obj i)
        ((oneDirectionInverseInputIdentityChoicesIso r F i).hom.app (Opposite.op ⦋0⦌) v) =
      oneDirectionInverseMixedMap r (F.map (𝟙 i)) v := by
  apply (familyVertexEquiv ((boundaryKanRealizationFunctor r).obj (F.obj i))
    ((oneDirectionKanRealizationFunctor r).obj (F.obj i))).injective
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (oneDirectionInverseInputIdentityChoicesIso_family r F i)
      (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact (pointedMappingPathInverseFamily_vertex
    ((oneDirectionKanComparisonNat r).app (F.obj i)) _).symm.trans
      (h.trans (oneDirectionInverseMixedFamily_vertex r (F.map (𝟙 i)) v))

end SerrePositivity.KST.SConstruction
