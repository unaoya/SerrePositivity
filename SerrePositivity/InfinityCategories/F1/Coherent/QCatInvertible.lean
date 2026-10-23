module

public import SerrePositivity.InfinityCategories.F1.Coherent.HomOrdinary
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：quasicategory の同値を Cat∞ の可逆な coherent 辺として検出する。
方針：関手同型の辺を元の内部 Hom の core へ持ち上げ、coherent Hom 比較で送る。
規約：Hom は core であり、関手空間全体を Kan と仮定しない。
使われ方：Cat∞ 値の図式間の自然な比較を coherent な同型へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 関手同型で結ばれた実際の射は Cat∞ のホモトピー圏で同じ射を表す。 -/
lemma coherentQCatEdge_homMk_eq_of_functorIso {K L : QCat.{u}}
    {f g : K ⟶ L} (h : FunctorIso f g) :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated := by
  let t : (SimplicialCategory.sHom K L) _⦋1⦌ :=
    ⟨(FunctorIso.edge h).edge, (quasicategoryCore_mem_edge_iff _).mpr
      ((isInvertibleEdge_congr
        (e := FunctorIso.edge h) (f := edgeOfSimplex (FunctorIso.edge h).edge) rfl).mp
          (FunctorIso.edge_isInvertible h))⟩
  let e₀ : SSet.Edge (SimplicialCategory.homEquiv' K L f)
      (SimplicialCategory.homEquiv' K L g) :=
    { edge := t
      src_eq := by apply Subtype.ext; exact (FunctorIso.edge h).src_eq
      tgt_eq := by apply Subtype.ext; exact (FunctorIso.edge h).tgt_eq }
  let e : SSet.Edge
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
      (ULift.up (SimplicialCategory.homEquiv' K L f))
      (ULift.up (SimplicialCategory.homEquiv' K L g)) :=
    SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e₀.toTruncated)
  have hp := congrArg (pinchedHomPiZeroToHom (coherentNerveVertex K) (coherentNerveVertex L))
    (SSet.π₀.sound (e.map (coherentHomComparison K L)))
  change SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _
    ((coherentHomComparison K L).app _ (ULift.up (SimplicialCategory.homEquiv' K L f)))) =
      SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _
        ((coherentHomComparison K L).app _ (ULift.up (SimplicialCategory.homEquiv' K L g)))) at hp
  have hf : pinchedHomVertexEquiv _ _
      ((coherentHomComparison K L).app _ (ULift.up (SimplicialCategory.homEquiv' K L f))) =
      (coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary f
  have hg : pinchedHomVertexEquiv _ _
      ((coherentHomComparison K L).app _ (ULift.up (SimplicialCategory.homEquiv' K L g))) =
      (coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary g
  exact (congrArg₂ Eq (congrArg SSet.Truncated.HomotopyCategory.homMk hf)
    (congrArg SSet.Truncated.HomotopyCategory.homMk hg)).mp hp

/-- 概要：quasicategory の同値の coherent な辺は可逆。
方針：逆射を coherent な辺にし、関手同型の合成条件をホモトピー圏の逆条件へ写す。
規約：指定された射 f 自体の辺について述べる。
使われ方：Kerodon Remark 3.1.6.3、Corollary 5.6.0.6、transport の同値性から辺の可逆性へ戻る。 -/
lemma coherentQCatEdge_isInvertible_of_isQCatEquivalence {K L : QCat.{u}}
    {f : K ⟶ L} (hf : IsQCatEquivalence f) : IsInvertibleEdge (coherentNerveEdge f) := by
  obtain ⟨g₀, ⟨hu⟩, ⟨hc⟩⟩ := hf
  let g : L ⟶ K := g₀
  change FunctorIso (f ≫ g) (𝟙 K) at hu
  change FunctorIso (g ≫ f) (𝟙 L) at hc
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated, ?_, ?_⟩⟩
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge (f ≫ g)).toTruncated :=
        (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (coherentNerveCompStruct f g).toTruncated)
      _ = SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge (𝟙 K)).toTruncated :=
        coherentQCatEdge_homMk_eq_of_functorIso hu
      _ = 𝟙 _ := by simp only [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge (g ≫ f)).toTruncated :=
        (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (coherentNerveCompStruct g f).toTruncated)
      _ = SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge (𝟙 L)).toTruncated :=
        coherentQCatEdge_homMk_eq_of_functorIso hc
      _ = 𝟙 _ := by simp only [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]

end SerrePositivity.InfinityCategories
