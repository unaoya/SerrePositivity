module
public import SerrePositivity.KST.SConstruction.BoundaryKComparison
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence

/-! # 元の正反復実現から境界商 Kan 模型への同値不変性
概要：元の正反復 S 実現の局所化同型を、同じ射の境界商・Kan・loop へ移す。
方針：自然な商射の可逆性を打ち消し、既存の Kan 置換と loop の比較へ渡す。
規約：各段の元の射を保持する。使われ方：実 BF K 射の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
variable {X Y : StableModel.{u}} (f : X ⟶ Y)

/-- 元の反復実現の局所化同型は、同じ射の全零境界商へ移る。 -/
lemma boundaryReducedRealizationMap_localized_isIso (r : ℕ)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((boundaryReducedRealizationMap r f).right)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hX := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have hY := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r Y
  have h := congrArg Q.map (boundaryReducedRealizationMap_quotient r f)
  rw [Q.map_comp, Q.map_comp] at h
  have : IsIso (Q.map (boundaryReductionQuotient r X) ≫
      Q.map ((boundaryReducedRealizationMap r f).right)) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

/-- 元の反復実現の局所化同型は、境界商 Kan 模型の全基点 π_* 同型を与える。 -/
lemma boundaryKanRealizationMap_piIsomorphism (r : ℕ)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map f))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (((boundaryKanRealizationFunctor r).map f).right) :=
  pointedKanReplacement_map_piIsomorphism_of_localized_isIso _
    (boundaryReducedRealizationMap_localized_isIso f r hf)

/-- 零段の loop においても、元の射は全基点 π_* 同型を誘導する。 -/
lemma boundaryKSpaceMap_piIsomorphism
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor 1).map f))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((boundaryKSpaceFunctor.map f).right) :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    ((boundaryKanRealizationFunctor 0).map f) (boundaryKanRealizationMap_piIsomorphism f 0 hf)

end SerrePositivity.KST.SConstruction
