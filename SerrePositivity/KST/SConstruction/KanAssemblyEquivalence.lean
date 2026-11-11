module
public import SerrePositivity.KST.SConstruction.ZeroRowLoopLocalized
public import SerrePositivity.KST.SConstruction.ZeroRowAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.KanAssemblySequence

/-! # 元の suspension 随伴の正の Ω 条件
概要：元の Kan 標的への随伴射は局所化同型であり、元の Kan 延長は全基点 π 同型になる。
方針：零行 loop との厳密な式で同型性を移し、元の源の Kan 単位と前段比較を合成する。
規約：元の構造射と全ての延長の選択を保つ。使われ方：BF 連結 K スペクトルへの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 元の Kan 標的への随伴射は追加仮定なしで局所化同型。 -/
lemma kanTargetAssemblyAdjoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((kanTargetAssemblyAdjointNat r).app X).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  let a := (sOneInnerOuterRealizationIso (r + 1) X).hom ≫ oneDirectionReductionQuotient r X
  let j := (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
    (PointedKanReplacement.functor.map (cyclicBoundaryIso (r + 1) X).hom)
  have hq : IsIso (Q.map (oneDirectionReductionQuotient r X)) :=
    oneDirectionReductionQuotient_image_isIso Q (Localization.inverts Q anodyneExtensions) r X
  have ha : IsIso (Q.map a) := by
    change IsIso (Q.map ((sOneInnerOuterRealizationIso (r + 1) X).hom ≫ _))
    rw [Q.map_comp]
    infer_instance
  have hl : IsIso (Q.map (zeroRowLoopComparison (r + 1) X)) :=
    zeroRowLoopComparison_localized_isIso r X
  have hj : IsIso (Q.map j.right) := by infer_instance
  have he : a ≫ ((kanTargetAssemblyAdjointNat r).app X).right =
      zeroRowLoopComparison (r + 1) X ≫ j.right := by
    rw [Category.assoc]
    exact zeroRowLoopComparison_assemblyAdjoint r X
  have hc : IsIso (Q.map a ≫ Q.map ((kanTargetAssemblyAdjointNat r).app X).right) := by
    rw [← Q.map_comp, he, Q.map_comp]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hc

/-- 元の随伴射の源の Kan 置換への任意の厳密な延長は全基点 π 同型。 -/
lemma kanAssemblyAdjointAt_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAssemblyAdjointAt r X v).right := by
  let Q := AnodyneHomotopy.anodyneQ
  let i := PointedKanReplacement.unit.app (oneDirectionReducedRealization r X)
  have hi : IsIso (Q.map i.right) :=
    (Localization.inverts Q anodyneExtensions) _ (PointedKanReplacement.unit_anodyne _)
  have hf : i.right ≫ (kanAssemblyAdjointAt r X v).right =
      ((kanTargetAssemblyAdjointNat r).app X).right :=
    congrArg Under.Hom.right (kanAssemblyAdjointAt_fac r X v)
  have hr := kanTargetAssemblyAdjoint_localized_isIso r X
  have hc : IsIso (Q.map i.right ≫ Q.map (kanAssemblyAdjointAt r X v).right) := by
    rw [← Q.map_comp, hf]
    exact hr
  exact kanPiIsomorphism_of_localized_isIso (kanAssemblyAdjointAt r X v).right
    ((isIso_comp_left_iff _ _).mp hc)

/-- 元の既存の境界商 Kan 列の構造射の随伴は全基点 π 同型。 -/
lemma boundaryKanAssemblyAdjoint_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryKanAssemblyAdjoint r X).right :=
  (oneDirectionKanComparisonInverse_piIsomorphism r X).comp
    (kanAssemblyAdjointAt_piIsomorphism r X _)

end SerrePositivity.KST.SConstruction
