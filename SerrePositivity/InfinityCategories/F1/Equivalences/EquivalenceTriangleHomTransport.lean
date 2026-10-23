module

public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceTriangleHomSpan
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTransportTriangleCoherence

/-!
概要：元の可逆三角形の三つの比較 span の指定された切断による Hom 輸送。
方針：同じ共通の三角形 Hom 上で元の頂点評価を厳密に回収する。
規約：切断を選び直さず、指定された三つの切断そのものを使う。
使われ方：元の底変換比較 span の合成の関手同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (Y : SSet.{u}) [Quasicategory Y] (x y : (equivalenceTriangle Y) _⦋0⦌)
  (s : ∀ i : Fin 3,
    intervalMappingSpace ((equivalenceTriangleEvaluation Y (i.succAbove 1)).app _ x)
      ((equivalenceTriangleEvaluation Y (i.succAbove 1)).app _ y) ⟶
    intervalMappingSpace ((equivalenceTriangleFace Y i).app _ x)
      ((equivalenceTriangleFace Y i).app _ y))
  (hs : ∀ i, s i ≫ equivalenceTriangleHomFaceEndpoint Y i 1 x y = 𝟙 _)

/-- 同じ面の比較 span の指定された切断で、終点の Hom を始点の Hom へ運ぶ。 -/
def equivalenceTriangleHomSectionTransport (i : Fin 3) :
    intervalMappingSpace ((equivalenceTriangleEvaluation Y (i.succAbove 1)).app _ x)
      ((equivalenceTriangleEvaluation Y (i.succAbove 1)).app _ y) ⟶
    intervalMappingSpace ((equivalenceTriangleEvaluation Y (i.succAbove 0)).app _ x)
      ((equivalenceTriangleEvaluation Y (i.succAbove 0)).app _ y) :=
  s i ≫ equivalenceTriangleHomFaceEndpoint Y i 0 x y

include hs in
/-- 同じ指定切断による各面の Hom 輸送は同値。 -/
lemma equivalenceTriangleHomSectionTransport_isQCatEquivalence (i : Fin 3) :
    IsQCatEquivalence (equivalenceTriangleHomSectionTransport Y x y s i) := by
  have : TrivialKanFibration (equivalenceTriangleHomFaceEndpoint Y i 1 x y) :=
    equivalenceTriangleHomFaceEndpoint_trivialKanFibration Y i 1 x y
  have h : IsQCatEquivalence (s i) := by
    apply (isQCatEquivalence_of_trivialKanFibration
      (equivalenceTriangleHomFaceEndpoint Y i 1 x y)).cancel_right
    rw [hs i]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have : TrivialKanFibration (equivalenceTriangleHomFaceEndpoint Y i 0 x y) :=
    equivalenceTriangleHomFaceEndpoint_trivialKanFibration Y i 0 x y
  exact h.comp (isQCatEquivalence_of_trivialKanFibration _)

/-- 同じ切断による各面の輸送は、共通の三角形 Hom からの元の頂点評価と整合する。 -/
def equivalenceTriangleHomSectionTransportFactorIso (i : Fin 3) :
    FunctorIso
      (equivalenceTriangleHomEvaluation Y (i.succAbove 1) x y ≫
        equivalenceTriangleHomSectionTransport Y x y s i)
      (equivalenceTriangleHomEvaluation Y (i.succAbove 0) x y) := by
  have : TrivialKanFibration (equivalenceTriangleHomFaceEndpoint Y i 1 x y) :=
    equivalenceTriangleHomFaceEndpoint_trivialKanFibration Y i 1 x y
  rw [← equivalenceTriangleHomFaceEndpoint_factor Y i 1 x y,
    ← equivalenceTriangleHomFaceEndpoint_factor Y i 0 x y]
  exact homSpanSectionTransportFactorIso
    (equivalenceTriangleHomFaceEndpoint Y i 1 x y)
    (equivalenceTriangleHomFaceEndpoint Y i 0 x y) (s i)
    (isFullyFaithful_of_trivialKanFibration _) (hs i)
    (equivalenceTriangleHomFace Y i x y)

/-- 指定された元の三つの切断による Hom 輸送は、同じ三角形で合成に関して同型。 -/
def equivalenceTriangleHomSectionTransportCompositionIso :
    FunctorIso
      (equivalenceTriangleHomSectionTransport Y x y s 0 ≫
        equivalenceTriangleHomSectionTransport Y x y s 2)
      (equivalenceTriangleHomSectionTransport Y x y s 1) := by
  apply homTransportTriangleCoherence
    (equivalenceTriangleHomEvaluation Y 0 x y)
    (equivalenceTriangleHomEvaluation Y 1 x y)
    (equivalenceTriangleHomEvaluation Y 2 x y)
  · exact equivalenceTriangleHomEvaluation_isQCatEquivalence Y 2 x y
  · exact equivalenceTriangleHomSectionTransportFactorIso Y x y s hs 2
  · exact equivalenceTriangleHomSectionTransportFactorIso Y x y s hs 0
  · exact equivalenceTriangleHomSectionTransportFactorIso Y x y s hs 1

end SerrePositivity.InfinityCategories
