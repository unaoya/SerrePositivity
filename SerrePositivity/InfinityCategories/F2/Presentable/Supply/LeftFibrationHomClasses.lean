module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.Core.UniverseEdgeTransport

/-!
概要：left fibrations の実射の coherent な辺の類の等式から、元の相対 Hom 内の同型を戻す。
方針：coherent Hom 比較の連結成分での単射性と Kan 複体の頂点同型の判定を使う。
規約：実射の底を固定する。使われ方：分類後の Hom の単射性を実相対 Hom の制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：coherent な辺の類が等しい実射は、元の相対 Hom 内で同型。
方針：coherent Hom 比較の連結成分を反映し、得た持ち上げた頂点同型を元の宇宙へ戻す。
規約：底を保つ元の二射を使う。使われ方：実相対 Hom の分類による単射性。 -/
lemma relativeVertexIso_of_leftFibrationEdge_homEq
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f g : E ⟶ H) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated =
      Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q g hg).toTruncated) :
    Nonempty (VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg)) := by
  let X := leftFibrationObjectOf p
  let Y := leftFibrationObjectOf q
  let c := coherentHomComparison X Y
  have hv (t : E ⟶ H) (ht : t ≫ q = p) :
      pinchedHomVertexEquiv (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)
        (c.app (Opposite.op ⦋0⦌) (ULift.up (relativeFunctorVertex q p t ht))) =
          (leftFibrationInfinityEdge p q t ht).toTruncated := by
    apply Truncated.Edge.ext
    have he := coherentHomComparison_ordinary
      (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from Over.homMk t ht)
    rw [leftFibrationHom_vertex] at he
    exact he
  have hc : SSet.mapπ₀ c (SSet.π₀.mk (ULift.up (relativeFunctorVertex q p f hf))) =
      SSet.mapπ₀ c (SSet.π₀.mk (ULift.up (relativeFunctorVertex q p g hg))) := by
    apply (pinchedHomPiZeroEquiv (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex q)).injective
    change Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv _ _ (c.app _ (ULift.up (relativeFunctorVertex q p f hf)))) =
      Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv _ _ (c.app _ (ULift.up (relativeFunctorVertex q p g hg))))
    exact (congrArg Truncated.HomotopyCategory.homMk (hv f hf)).trans
      (h.trans (congrArg Truncated.HomotopyCategory.homMk (hv g hg)).symm)
  have he := (coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective.1 hc
  obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq he
  exact ⟨(UniverseEdge.downFunctor.{u, u + 1} (relativeFunctorSpace q p)).mapIso e⟩

end SerrePositivity.InfinityCategories.F2.Presentable
