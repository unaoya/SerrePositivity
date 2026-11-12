module
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedChoices
public import SerrePositivity.KST.Spectra.PointedMappingHomotopy

/-! # 混合切断からの比較逆射の自然性
概要：両端の逆射の選択を同じ混合切断空間で結び、写像空間の辺を回収する。
方針：切断の移送の頂点の式と mapping path の射影の自然性を使う。
規約：全ての指定した逆射選択を保持する。
使われ方：スペクトルの構造射に含まれる逆射の高次比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 源から移した混合切断は元の逆射の後合成を回収する。 -/
lemma oneDirectionInverseMixedFromSource_map (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌) :
    oneDirectionInverseMixedMap r f
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v) =
    oneDirectionKanInverseAt r X v ≫ (oneDirectionKanRealizationFunctor r).map f := by
  have h := pointedLiftTransport_vertex
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app X)) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)
    (𝟙 _) (oneDirectionMappingPathMap r f) ((boundaryKanRealizationFunctor r).map f)
    (oneDirectionMappingPathMap_projection r f) (by simp) v
  have hh := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))
    (h.trans (Category.id_comp _))
  refine hh.trans ?_
  rw [Category.assoc, oneDirectionMappingPathMap_retraction, ← Category.assoc]
  rfl

/-- 標的から移した混合切断は元の逆射の前合成を回収する。 -/
lemma oneDirectionInverseMixedFromTarget_map (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r Y) _⦋0⦌) :
    oneDirectionInverseMixedMap r f
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) v) =
    (boundaryKanRealizationFunctor r).map f ≫ oneDirectionKanInverseAt r Y v := by
  have h := pointedLiftTransport_vertex
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y)) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)
    ((boundaryKanRealizationFunctor r).map f) (𝟙 _) (𝟙 _) (by simp) (by simp) v
  have hh := h.trans (congrArg ((boundaryKanRealizationFunctor r).map f ≫ ·)
    (Category.comp_id _))
  exact (congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y)) hh).trans
    (Category.assoc _ _ _)

/-- 逆射の混合パラメーター族は各頂点で混合写像を回収する。 -/
lemma oneDirectionInverseMixedFamily_vertex (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionInverseMixedChoices r f) _⦋0⦌) :
    (oneDirectionInverseMixedFamily r f).app (Opposite.op ⦋0⦌) v =
      familyVertex (oneDirectionInverseMixedMap r f v) := by
  let a := (pullback.fst
    (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))).right
    (SSet.yonedaEquiv.symm (familyVertex ((boundaryKanRealizationFunctor r).map f)))).app
    (Opposite.op ⦋0⦌) v
  have ha : a = familyVertex
      (pointedLiftMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
        ((boundaryKanRealizationFunctor r).map f) v) :=
    (familyVertex_familyMap _ _ a).symm
  exact (congrArg ((PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))).right.app
      (Opposite.op ⦋0⦌)) ha).trans (familyVertex_post _ _)

/-- 指定した両端の逆射は混合切断空間内の実際の辺で比較できる。 -/
lemma oneDirectionInverseMixedChoices_nonempty_edge (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌) :
    Nonempty ((oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w)) := by
  obtain ⟨e⟩ := ((oneDirectionInverseMixedChoices_isContractibleKan r f).isTerminalVertex
    ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w)).nonempty_edge
    ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v)
  exact ⟨SSet.Edge.ofTruncated e⟩

/-- 混合切断の辺を、指定した比較逆射の自然性の写像空間の辺へ写す。 -/
lemma oneDirectionKanInverseAt_naturality_edge (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌) :
    Nonempty ((PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((oneDirectionKanRealizationFunctor r).obj Y)).right.Edge
      (familyVertex (oneDirectionKanInverseAt r X v ≫ (oneDirectionKanRealizationFunctor r).map f))
      (familyVertex ((boundaryKanRealizationFunctor r).map f ≫ oneDirectionKanInverseAt r Y w))) := by
  obtain ⟨e⟩ := oneDirectionInverseMixedChoices_nonempty_edge r f v w
  refine ⟨(e.map (oneDirectionInverseMixedFamily r f)).ofEq ?_ ?_⟩
  · exact (oneDirectionInverseMixedFamily_vertex r f _).trans
      (congrArg familyVertex (oneDirectionInverseMixedFromSource_map r f v))
  · exact (oneDirectionInverseMixedFamily_vertex r f _).trans
      (congrArg familyVertex (oneDirectionInverseMixedFromTarget_map r f w))

/-- 任意の指定した逆射選択は入力に関して実際の基点固定ホモトピーで自然。 -/
lemma oneDirectionKanInverseAt_naturality_homotopy (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌) :
    ∃ H : SSet.Homotopy
        (oneDirectionKanInverseAt r X v ≫ (oneDirectionKanRealizationFunctor r).map f).right
        ((boundaryKanRealizationFunctor r).map f ≫ oneDirectionKanInverseAt r Y w).right,
      ((boundaryKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((oneDirectionKanRealizationFunctor r).obj Y).hom := by
  obtain ⟨e⟩ := oneDirectionKanInverseAt_naturality_edge r f v w
  exact ⟨homotopyOfEdge e, homotopyOfEdge_base e⟩

end SerrePositivity.KST.SConstruction
