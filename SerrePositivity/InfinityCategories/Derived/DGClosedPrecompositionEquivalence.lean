module
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEdges
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 可逆な実閉辺による全 Hom と pinched Hom の前合成同値

概要：H⁰ で可逆な閉射の全 Hom 前合成は準同型、実 pinched 前合成はホモトピー同値。
方針：Yoneda の全 Hom 同型と、代表加群間の射影的な前合成へ移す。
規約：前三角性・商の平坦性は不要。使われ方：商側の屋根図式の全細分の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- H⁰ で可逆な閉射による全 Hom 鎖前合成は準同型。 -/
lemma dgClosedPrecomposition_quasiIso_of_homotopyIso {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    [IsIso ((toHomotopy A D).map s)] : QuasiIso (dgClosedPrecomposition A D (y := y) s) := by
  let f := (dgYoneda A D).onClosed.map s
  have hi : IsIso ((moduleToHomotopy A D).map f) := by
    change IsIso ((dgYoneda A D).onHomotopy.map ((toHomotopy A D).map s))
    infer_instance
  have hf : moduleQuasiIso A D f := by
    apply (moduleHomotopyQuasiIso_map_iff A D f).mp
    intro z i
    change IsIso ((moduleHomotopyHomology A D z i).map ((moduleToHomotopy A D).map f))
    infer_instance
  have := moduleHomotopicallyProjective_precompose_quasiIso A D
    (representable_homotopicallyProjective A D q) (representable_homotopicallyProjective A D x)
    f hf (ForgetEnrichment.of (Complex A) (representable A y))
  have : IsIso (yonedaHom A D x y) := by
    dsimp only [yonedaHom]
    infer_instance
  dsimp only [dgClosedPrecomposition]
  infer_instance

/-- 可逆な実閉辺による全 Hom 鎖前合成は準同型。 -/
lemma dgClosedPrecomposition_quasiIso_of_invertible {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hs : IsInvertibleEdge (X := dgNerve A D) (dgClosedEdge A D s)) :
    QuasiIso (dgClosedPrecomposition A D (y := y) s) := by
  have hi : IsIso ((dgStableHomotopyEquivalence A D).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (dgClosedEdge A D s))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk (dgClosedEdge A D s)) := hs
    infer_instance
  rw [dgStableHomotopyEquivalence_map_homMk, dgClosedEdge_closed] at hi
  exact dgClosedPrecomposition_quasiIso_of_homotopyIso A D s

/-- 可逆な実閉辺による pinched 前合成は実ホモトピー同値。 -/
lemma pinchedClosedPrecomposition_equivalence_of_invertible {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hs : IsInvertibleEdge (X := dgNerve A D) (dgClosedEdge A D s)) :
    IsSimplicialHomotopyEquivalence (pinchedClosedPrecomposition A D (y := y) s) := by
  have := dgClosedPrecomposition_quasiIso_of_invertible A D (y := y) s hs
  exact pinchedHomChainMap_quasiIso_equivalence (dgClosedPrecomposition A D s)

end SerrePositivity.InfinityCategories
