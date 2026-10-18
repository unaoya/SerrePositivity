module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionHomotopy

/-!
概要：底上の前合成同値の span から left fibration への実際の比較射を得る。
方針：相対関手空間の前合成の本質的全射性で射を選び、制限の同型と二対三則で同値性を示す。
規約：得られる射は底を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元 span を一つの比較射へ置き換える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の前合成同値の span の標的が left fibration なら、二端点を結ぶ底上の前合成同値射が存在する。
方針：共通の始域での射を相対関手空間の同値で戻し、制限を元の比較と可逆なホモトピーで結ぶ。
規約：p の left fibration 性や始域の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、coherent な表現との直接の底上の比較。 -/
lemma exists_leftFibration_comparison_of_span
    {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    ∃ f : E ⟶ F, f ≫ q = p ∧ IsPrecompositionEquivalence f := by
  have : Quasicategory F := quasicategory_of_innerFibration q
  let a' : Over.mk r ⟶ Over.mk p := Over.homMk a ha
  have he := relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨h⟩⟩ := he.choose.isEssentiallySurjective (relativeFunctorVertex q r b hb)
  obtain ⟨f, hf, hv⟩ := exists_relativeFunctorVertex q p v
  rw [← hv] at h
  have h' : FunctorIso (a ≫ f) b :=
    h.map (vertexFiberι ((ihom Z).map q) (functorVertex r))
  have hcomp : IsPrecompositionEquivalence (a ≫ f) :=
    (isPrecompositionEquivalence_iff_of_homotopy h'.simplicialHomotopy
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge h') (FunctorIso.edge_isInvertible h'))).mpr eb
  exact ⟨f, hf, ea.cancel_left hcomp⟩

end SerrePositivity.InfinityCategories
