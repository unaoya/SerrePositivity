module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityFamilyChoices
public import SerrePositivity.KST.Spectra.PointedMappingHomotopy

/-! # 同時選択した随伴構造射の実際の自然性
概要：任意に指定した両端の同時選択を、可縮な自然性パラメーター内の辺で結ぶ。
方針：全次数の両端回収を頂点で評価し、実際の写像空間の辺へ移す。
規約：自然性の族の延長選択も明示する。
使われ方：元の BF K 模型の構造射の高次比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 源の指定した同時選択の評価は元の随伴射の後合成。 -/
lemma boundaryAssemblyNaturalityFamilyAt_source_vertex (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    (boundaryAssemblyNaturalityFamilyAt r f u).app (Opposite.op ⦋0⦌)
      ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v) =
      familyVertex (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (boundaryAssemblyNaturalityFamilyAt_source r f u) (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  exact (congrArg ((PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
    ((loopBoundaryKanFunctor (r + 1)).map f)).right.app (Opposite.op ⦋0⦌))
      (boundaryKanAssemblyAdjointFamily_vertex r X v)).trans (familyVertex_post _ _)

/-- 標的の指定した同時選択の評価は元の随伴射の前合成。 -/
lemma boundaryAssemblyNaturalityFamilyAt_target_vertex (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r Y) _⦋0⦌) :
    (boundaryAssemblyNaturalityFamilyAt r f u).app (Opposite.op ⦋0⦌)
      ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) v) =
      familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y v) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (boundaryAssemblyNaturalityFamilyAt_target r f u) (Opposite.op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
    ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.app (Opposite.op ⦋0⦌))
      (boundaryKanAssemblyAdjointFamily_vertex r Y v)).trans (familyVertex_pre _ _)

/-- 指定した随伴構造射の同時選択は自然性の写像空間の実際の辺で結ばれる。 -/
lemma boundaryKanAssemblyAdjointAt_naturality_edge (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌) :
    Nonempty ((PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Y)).right.Edge
      (familyVertex (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f))
      (familyVertex ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w))) := by
  obtain ⟨e⟩ := ((boundaryAssemblyNaturalityParameters_isContractibleKan r f).isTerminalVertex
    ((boundaryAssemblyNaturalityTarget r f).app (Opposite.op ⦋0⦌) w)).nonempty_edge
    ((boundaryAssemblyNaturalitySource r f).app (Opposite.op ⦋0⦌) v)
  refine ⟨((SSet.Edge.ofTruncated e).map (boundaryAssemblyNaturalityFamilyAt r f u)).ofEq ?_ ?_⟩
  · exact boundaryAssemblyNaturalityFamilyAt_source_vertex r f u v
  · exact boundaryAssemblyNaturalityFamilyAt_target_vertex r f u w

/-- 同時選択の随伴構造射の自然性を実際の基点固定ホモトピーとして回収する。 -/
lemma boundaryKanAssemblyAdjointAt_naturality_homotopy (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (u : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌)
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (w : (boundaryKanAssemblyChoices r Y) _⦋0⦌) :
    ∃ H : SSet.Homotopy
        (boundaryKanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f).right
        ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjointAt r Y w).right,
      ((boundaryKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj Y).hom := by
  obtain ⟨e⟩ := boundaryKanAssemblyAdjointAt_naturality_edge r f u v w
  exact ⟨homotopyOfEdge e, homotopyOfEdge_base e⟩

end SerrePositivity.KST.SConstruction
