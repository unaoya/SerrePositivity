module

public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalization

/-!
概要：可逆な余単位を持つ実随伴の左関手の局所化普遍性。
方針：右随伴による制限を前合成の逆とし、元の単位と余単位で両合成を比較する。
規約：商の普遍性を入力しない。使われ方：K-8 の半直交分解からの Verdier 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.AdjointLocalization

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) [IsIso a.counit]

local instance counitHomIsIso : IsIso a.counitHom := by
  change IsIso ((qcatHomFunctor Y Y).map a.counit)
  infer_instance

def counitIso : FunctorIso (G ≫ F) (𝟙 Y) := asIso a.counitHom

/-- 概要：左随伴単位の選んだホモトピー代表の各成分は左随伴で反転される。
方針：左随伴で写した単位の h Fun の可逆性を成分へ移す。
規約：元の単位の代表を用いる。使われ方：反転関手上の単位による前合成の同型。 -/
lemma unitComponent_mem_invertedEdges (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (functorHomHomotopy a.unitHom) x).edge ∈
      invertedEdges F := by
  let H := functorHomotopyPostcomp (functorHomHomotopy a.unitHom) F
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (functorHomHomotopy a.unitHom) F)))
    rw [functorHomotopyPostcomp_hom, functorHomHomotopy_hom]
    exact a.unit_postcompLeft_isIso
  have h := homotopy_component_isInvertible_of_isIso H x
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex
    (simplicialHomotopyVertexEdge (functorHomHomotopy a.unitHom) x).edge).map
      ((truncation 2).map F))
    (f := (simplicialHomotopyVertexEdge H x).toTruncated) rfl).mpr h

/-- 概要：左随伴が反転する辺を反転する関手族上の、単位による前合成の自然同型。
方針：各関手が全ての単位成分を反転することを制限付き前合成の一般補題へ渡す。
規約：元の圏の全対象を局所と仮定しない。使われ方：局所化の逆合成。 -/
def invertingUnitPrecompositionIso (E : SSet.{u}) [Quasicategory E] :
    FunctorIso (invertingFunctors X E (invertedEdges F)).ι
      ((invertingFunctors X E (invertedEdges F)).ι ≫ (pre (F ≫ G)).app E) := by
  let K := invertingFunctors X E (invertedEdges F)
  have h := functorIsoRestrictedPrecompositionOfHomotopy (functorHomHomotopy a.unitHom) K.ι (by
    intro v u hu x
    have hv := fullSubcomplexOnVertices_vertex v
    change IsInvertingFunctorVertex X E (invertedEdges F) v.val at hv
    unfold IsInvertingFunctorVertex at hv
    rw [show v.val = (functorVertexEquiv X E) u from hu, Equiv.symm_apply_apply] at hv
    have hi := hv (unitComponent_mem_invertedEdges a x)
    exact (isInvertibleEdge_congr (e := (edgeOfSimplex
      (simplicialHomotopyVertexEdge (functorHomHomotopy a.unitHom) x).edge).map
        ((truncation 2).map u))
      (f := (simplicialHomotopyVertexEdge (functorHomHomotopy a.unitHom) x).toTruncated.map
        ((truncation 2).map u)) rfl).mp hi)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using h

/-- 概要：左随伴に沿う前合成の逆は右随伴に沿う制限。
方針：W を反転する関手を右随伴上で制限する。
規約：W は reflector 自身が反転する辺の集合。使われ方：局所化の普遍同値の逆射。 -/
def localizationRestriction (_a : QCatAdjunction F G) (E : SSet.{u}) :
    (invertingFunctors X E (invertedEdges F) : SSet.{u}) ⟶
      (ihom Y).obj E :=
  (invertingFunctors X E (invertedEdges F)).ι ≫
    (pre G).app E

/-- 概要：左随伴に沿う前合成と右随伴による制限は自然同値を与える。
方針：一方の合成は余単位、他方は反転関手上の単位で同型にする。
規約：局所化の存在を仮定せず、明示的な逆射を構成する。
使われ方：左随伴的局所化の普遍性。 -/
def localizationPrecompositionEquivalence (E : SSet.{u}) [Quasicategory E] :
    QCatEquivalence ((ihom Y).obj E)
      (invertingFunctors X E (invertedEdges F) : SSet.{u}) where
  hom := localizationPrecomposition F (invertedEdges F) (fun _ h => h) E
  inv := localizationRestriction a E
  homInvIso := by
    simpa only [localizationRestriction, ← Category.assoc, localizationPrecomposition_ι,
      pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using (counitIso a).map_pre E
  invHomIso := by
    let K := invertingFunctors X E (invertedEdges F)
    let U := localizationPrecomposition F (invertedEdges F) (fun _ h => h) E
    let V := localizationRestriction a E
    have h : FunctorIso ((𝟙 (K : SSet.{u})) ≫ K.ι) ((V ≫ U) ≫ K.ι) := by
      simpa only [V, U, K, localizationRestriction, Category.assoc, localizationPrecomposition_ι,
        pre_map, NatTrans.comp_app, Category.id_comp] using
        invertingUnitPrecompositionIso a E
    let hf := fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u}) ((ihom X).obj E)
      (IsInvertingFunctorVertex X E (invertedEdges F))
    exact (hf.preimageIso (X := HomotopyCategory.mk (functorVertex (𝟙 (K : SSet.{u}))))
      (Y := HomotopyCategory.mk (functorVertex (V ≫ U))) h).symm

include a

/-- 概要：左随伴は自身が反転する辺に関する局所化を表す。
方針：全標的での明示的な前合成の同値を局所化の定義へ渡す。
規約：任意の辺集合に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3 の左随伴的局所化の普遍性。 -/
lemma isLocalization : IsLocalization F (invertedEdges F) := by
  refine ⟨fun _ h => h, fun E _ => ?_⟩
  exact (localizationPrecompositionEquivalence a E).isQCatEquivalence

end SerrePositivity.KST.LocalizingInvariants.AdjointLocalization
