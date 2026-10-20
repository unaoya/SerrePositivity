module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionChainMap
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionEquivalence
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso

/-! # 可逆な実閉辺による全 Hom と pinched Hom の後合成同値

概要：可逆な実閉辺による元の Hom の後合成は準同型で、pinched Hom の実ホモトピー同値。
方針：代表加群からの Hom が準同型を保つことを全 Hom Yoneda 同型で移す。
規約：前三角性は不要。使われ方：商側で閉分母の後合成を有限図式ごと戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- H⁰ で可逆な閉射による全 Hom 鎖後合成は準同型。 -/
lemma dgClosedPostcomposition_quasiIso_of_homotopyIso {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    [IsIso ((toHomotopy A D).map s)] : QuasiIso (dgClosedPostcomposition A D (x := x) s) := by
  let f := (dgYoneda A D).onClosed.map s
  have hi : IsIso ((moduleToHomotopy A D).map f) := by
    change IsIso ((dgYoneda A D).onHomotopy.map ((toHomotopy A D).map s))
    infer_instance
  have hf : moduleQuasiIso A D f := by
    apply (moduleHomotopyQuasiIso_map_iff A D f).mp
    intro w i
    change IsIso ((moduleHomotopyHomology A D w i).map ((moduleToHomotopy A D).map f))
    infer_instance
  have := moduleHomotopicallyProjective_postcompose_quasiIso A D
    (representable_homotopicallyProjective A D x) f hf
  have : IsIso (yonedaHom A D x y) := by
    dsimp only [yonedaHom]
    infer_instance
  rw [dgClosedPostcomposition_yonedaConjugate]
  infer_instance

/-- 可逆な実閉辺による全 Hom 鎖後合成は準同型。 -/
lemma dgClosedPostcomposition_quasiIso_of_invertible {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    (hs : IsInvertibleEdge (X := dgNerve A D) (dgClosedEdge A D s)) :
    QuasiIso (dgClosedPostcomposition A D (x := x) s) := by
  have hi : IsIso ((dgStableHomotopyEquivalence A D).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (dgClosedEdge A D s))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk (dgClosedEdge A D s)) := hs
    infer_instance
  rw [dgStableHomotopyEquivalence_map_homMk, dgClosedEdge_closed] at hi
  exact dgClosedPostcomposition_quasiIso_of_homotopyIso A D s

/-- 指定閉射による、元の実 pinched Hom の後合成。 -/
def pinchedClosedPostcomposition {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    DGNerve.pinchedHom A D x y ⟶ DGNerve.pinchedHom A D x z :=
  pinchedHomChainMap (dgClosedPostcomposition A D s)

/-- 可逆な実閉辺による pinched 後合成は、実ホモトピー同値。 -/
lemma pinchedClosedPostcomposition_equivalence_of_invertible {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    (hs : IsInvertibleEdge (X := dgNerve A D) (dgClosedEdge A D s)) :
    IsSimplicialHomotopyEquivalence (pinchedClosedPostcomposition A D (x := x) s) := by
  have := dgClosedPostcomposition_quasiIso_of_invertible A D (x := x) s hs
  exact pinchedHomChainMap_quasiIso_equivalence (dgClosedPostcomposition A D s)

end SerrePositivity.InfinityCategories
