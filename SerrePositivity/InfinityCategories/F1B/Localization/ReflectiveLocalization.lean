module

public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.RestrictedPrecomposition

/-!
概要：反射は自身が反転する辺に関する局所化である。
方針：包含による制限を前合成の逆とし、余単位と反転関手上の単位で両合成を同型にする。
規約：任意の W に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3 の反射的局所化と Def 6.3.1.9 の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：h Fun の類が可逆なホモトピーは各点でも可逆。
方針：成分評価が同型を保つこととホモトピー成分の表示を使う。
規約：始域・標的の quasicategory 性は不要。
使われ方：反射で写した単位の成分の可逆性。 -/
lemma homotopy_component_isInvertible_of_isIso {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g)
    [IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))]
    (x : A _⦋0⦌) : IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  have h : IsIso (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) x) :=
    inferInstance
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (simplicialHomotopyVertexEdge H x).toTruncated)
  exact (functorHomEvaluate_homotopy H x) ▸ h

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : ReflectiveSubcategory X P)

/-- 概要：反射単位の選んだホモトピー代表の各成分は反射で反転される。
方針：反射で写した単位の h Fun の可逆性を成分へ移す。
規約：元の単位の代表を用いる。使われ方：反転関手上の単位による前合成の同型。 -/
lemma unitComponent_mem_invertedEdges (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (functorHomHomotopy r.unit) x).edge ∈
      invertedEdges r.reflector := by
  let H := functorHomotopyPostcomp (functorHomHomotopy r.unit) r.reflector
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (functorHomHomotopy r.unit) r.reflector)))
    rw [functorHomotopyPostcomp_hom, functorHomHomotopy_hom]
    exact r.adjunction.unit_postcompLeft_isIso
  have h := homotopy_component_isInvertible_of_isIso H x
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex
    (simplicialHomotopyVertexEdge (functorHomHomotopy r.unit) x).edge).map
      ((truncation 2).map r.reflector))
    (f := (simplicialHomotopyVertexEdge H x).toTruncated) rfl).mpr h

/-- 概要：反射が反転する辺を反転する関手族上の、単位による前合成の自然同型。
方針：各関手が全ての単位成分を反転することを制限付き前合成の一般補題へ渡す。
規約：元の圏の全対象を局所と仮定しない。使われ方：局所化の逆合成。 -/
def invertingUnitPrecompositionIso (E : SSet.{u}) [Quasicategory E] :
    FunctorIso (invertingFunctors X E (invertedEdges r.reflector)).ι
      ((invertingFunctors X E (invertedEdges r.reflector)).ι ≫ (pre r.localization).app E) := by
  let K := invertingFunctors X E (invertedEdges r.reflector)
  have h := functorIsoRestrictedPrecompositionOfHomotopy (functorHomHomotopy r.unit) K.ι (by
    intro v u hu x
    have hv := fullSubcomplexOnVertices_vertex v
    change IsInvertingFunctorVertex X E (invertedEdges r.reflector) v.val at hv
    unfold IsInvertingFunctorVertex at hv
    rw [show v.val = (functorVertexEquiv X E) u from hu, Equiv.symm_apply_apply] at hv
    have hi := hv (r.unitComponent_mem_invertedEdges x)
    exact (isInvertibleEdge_congr (e := (edgeOfSimplex
      (simplicialHomotopyVertexEdge (functorHomHomotopy r.unit) x).edge).map ((truncation 2).map u))
      (f := (simplicialHomotopyVertexEdge (functorHomHomotopy r.unit) x).toTruncated.map
        ((truncation 2).map u)) rfl).mp hi)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using h

/-- 概要：反射に沿う前合成の逆は包含に沿う制限。
方針：W を反転する関手を包含上で制限する。
規約：W は reflector 自身が反転する辺の集合。使われ方：局所化の普遍同値の逆射。 -/
def localizationRestriction (E : SSet.{u}) :
    (invertingFunctors X E (invertedEdges r.reflector) : SSet.{u}) ⟶
      (ihom (fullSubcomplexOnVertices X P : SSet.{u})).obj E :=
  (invertingFunctors X E (invertedEdges r.reflector)).ι ≫
    (pre (fullSubcomplexOnVertices X P).ι).app E

/-- 概要：反射に沿う前合成と包含による制限は自然同値を与える。
方針：一方の合成は余単位、他方は反転関手上の単位で同型にする。
規約：局所化の存在を仮定せず、明示的な逆射を構成する。
使われ方：反射的局所化の普遍性。 -/
def localizationPrecompositionEquivalence (E : SSet.{u}) [Quasicategory E] :
    QCatEquivalence ((ihom (fullSubcomplexOnVertices X P : SSet.{u})).obj E)
      (invertingFunctors X E (invertedEdges r.reflector) : SSet.{u}) where
  hom := localizationPrecomposition r.reflector (invertedEdges r.reflector) (fun _ h => h) E
  inv := r.localizationRestriction E
  homInvIso := by
    simpa only [localizationRestriction, ← Category.assoc, localizationPrecomposition_ι,
      pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using r.counitIso.map_pre E
  invHomIso := by
    let K := invertingFunctors X E (invertedEdges r.reflector)
    let U := localizationPrecomposition r.reflector (invertedEdges r.reflector) (fun _ h => h) E
    let V := r.localizationRestriction E
    have h : FunctorIso ((𝟙 (K : SSet.{u})) ≫ K.ι) ((V ≫ U) ≫ K.ι) := by
      simpa only [V, U, K, localizationRestriction, Category.assoc, localizationPrecomposition_ι,
        localization, pre_map, NatTrans.comp_app, Category.id_comp] using
        r.invertingUnitPrecompositionIso E
    let hf := fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u}) ((ihom X).obj E)
      (IsInvertingFunctorVertex X E (invertedEdges r.reflector))
    exact (hf.preimageIso (X := HomotopyCategory.mk (functorVertex (𝟙 (K : SSet.{u}))))
      (Y := HomotopyCategory.mk (functorVertex (V ≫ U))) h).symm

/-- 概要：反射は自身が反転する辺に関する局所化を表す。
方針：全標的での明示的な前合成の同値を局所化の定義へ渡す。
規約：任意の辺集合に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3 の反射的局所化の普遍性。 -/
lemma isLocalization : IsLocalization r.reflector (invertedEdges r.reflector) := by
  refine ⟨fun _ h => h, fun E _ => ?_⟩
  exact (r.localizationPrecompositionEquivalence E).isQCatEquivalence

end ReflectiveSubcategory
end SerrePositivity.InfinityCategories
