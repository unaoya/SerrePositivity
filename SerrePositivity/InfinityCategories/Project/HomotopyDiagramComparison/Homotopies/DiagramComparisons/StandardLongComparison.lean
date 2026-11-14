module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PointTransportComparisonEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：同じ根辺に合成する二つの元の二単体の標準長辺を、同じ延長空間で比較する。
方針：両長辺から同じ標準根辺への比較を、可縮な始域で合成する。
規約：終点の類は元の二つの合成同型から計算する。使われ方：native な span の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma iso_comp_symm_hom_arrow {C : Type*} [Category* C]
    {a b c a' b' c' : C} (I : a ≅ c) (J : b ≅ c) (K : a' ≅ c') (L : b' ≅ c')
    (hI : Arrow.mk I.hom = Arrow.mk K.hom) (hJ : Arrow.mk J.hom = Arrow.mk L.hom) :
    Arrow.mk (I ≪≫ J.symm).hom = Arrow.mk (K ≪≫ L.symm).hom := by
  obtain ⟨ha, hc, hI⟩ := (Arrow.mk_eq_mk_iff _ _).mp hI
  subst a' c'
  obtain ⟨hb, _, hJ⟩ := (Arrow.mk_eq_mk_iff _ _).mp hJ
  subst b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hI hJ
  have hK : I = K := Iso.ext hI
  have hL : J = L := Iso.ext hJ
  subst K L
  rfl

/-- 可縮な始域の比較の像を、同じ中継頂点を通る二比較の像で計算する。 -/
lemma contractibleVertexIso_endpoint_factor {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) (x y z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x z) F ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso y z) F).symm := by
  have he : hX.vertexIso x y = hX.vertexIso x z ≪≫ (hX.vertexIso y z).symm := by
    have := hX.kanComplex
    apply Iso.ext
    exact (hX.isTerminalVertex y).isTerminalHo.hom_ext _ _
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm]

variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b b' c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c}
  {e' : B.Edge a b'} {f' : B.Edge b' c} {g : B.Edge a c}
  (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (σ : SSet.Edge.CompStruct e f g)
  (τ : SSet.Edge.CompStruct e' f' g)
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionSpace_isContractibleKan p g v
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionEndpoint p g v
local notation "x" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPointExtensionVertex p v σ
local notation "y" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPointExtensionVertex p v τ
local notation "z" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointExtensionVertex p g v
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionIso p σ
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionIso p τ

/-- 元の二つの標準長辺を、同じ根辺の固定延長空間で比較する。 -/
def coherentTransportStandardLongComparisonIso := (hS).vertexIso x y

/-- 同じ根辺空間の比較の終点は、元の二つの合成比較の合成の同じ成分である。 -/
lemma coherentTransportStandardLongComparisonIso_endpoint_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (coherentTransportStandardLongComparisonIso p v σ τ) F).hom =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso ((I) ≪≫ (J).symm)).hom.app (SSet.HomotopyCategory.mk v)) := by
  have hI := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointCanonicalComparison_endpoint_hom_arrow p v σ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoComponent_hom_arrow I v)
  have hJ := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointCanonicalComparison_endpoint_hom_arrow p v τ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoComponent_hom_arrow J v)
  have hF := contractibleVertexIso_endpoint_factor hS F x y z
  refine (congrArg (fun K ↦ Arrow.mk K.hom) hF).trans ?_
  refine (iso_comp_symm_hom_arrow _ _ _ _ hI hJ).trans ?_
  have hM := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans I (J).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).trans
    (congrArg (fun K ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) ≪≫ K)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm J (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)))
  exact (congrArg (fun K ↦ Arrow.mk K.hom) hM).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoComponent_hom_arrow ((I) ≪≫ (J).symm) v).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
