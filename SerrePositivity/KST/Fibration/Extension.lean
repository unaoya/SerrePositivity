module
public import SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.WeakEquivalences
public import SerrePositivity.InfinityCategories.Stable.PretriangulatedInstance
public import SerrePositivity.InfinityCategories.Stable.HomotopyNatTransPrecomposition

/-! # W の拡大安定性

実 cofiber 四角形の間の単体的ホモトピーを入力にする。商で写した実四角形から
三角形の射を構成し、その両端の同型性から元の中間成分の W 所属を得る。
商の普遍性や写像空間の比較をホモトピー圏で代用するものではない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- ホモトピーの指定頂点を通る実縦辺。 -/
def componentEdge {J X : SSet.{u}} {F G : J ⟶ X}
    (H : SSet.Homotopy F G) (a : J _⦋0⦌) :=
  (((Truncated.Edge.id (X := (truncation 2).obj J) a).tensor
    homotopyIntervalEdge).map ((truncation 2).map H.h))

/-- 指定両端の輸送は成分の可逆性を変えない。 -/
lemma componentEdge_isInvertible_iff {J X : SSet.{u}} {F G : J ⟶ X}
    (H : SSet.Homotopy F G) (a : J _⦋0⦌) :
    IsInvertibleEdge (componentEdge H a) ↔
      IsIso ((homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app
        (SSet.HomotopyCategory.mk a)) := by
  have he := homotopyNatTransOfEndpoints_app_arrow H.h H.h₀ H.h₁ a
  exact (congrArg (fun b : Arrow (hoFunctor.obj X) => IsIso b.hom) he).symm.to_iff

/-- cofiber 列の間の実ホモトピーでは、両端の W 所属から中間の W 所属が従う。 -/
theorem weakEquivalences_extension
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (t d : ZeroTriangle B.obj)
    (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (H : SSet.Homotopy t.square d.square)
    (h₀ : (componentEdge H
      (squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 0 0)).edge ∈ weakEquivalences i)
    (h₂ : (componentEdge H
      (squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 1 1)).edge ∈ weakEquivalences i) :
    (componentEdge H
      (squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 1 0)).edge ∈ weakEquivalences i := by
  let T := t.map q.hom (IsExactFunctor.preservesZero (F := q.hom))
  let D := d.map q.hom (IsExactFunctor.preservesZero (F := q.hom))
  have hT : IsCofiberSequence T := IsExactFunctor.preservesCofiber (F := q.hom) t ht
  have hD : IsCofiberSequence D := IsExactFunctor.preservesCofiber (F := q.hom) d hd
  let Q : SSet.Homotopy T.square D.square := {
    h := H.h ≫ q.hom
    h₀ := by rw [← Category.assoc, H.h₀]; rfl
    h₁ := by rw [← Category.assoc, H.h₁]; rfl }
  have hc (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
      IsInvertibleEdge ((componentEdge H a).map ((truncation 2).map q.hom)) ↔
        IsIso ((homotopyNatTransOfEndpoints Q.h Q.h₀ Q.h₁).app
          (SSet.HomotopyCategory.mk a)) :=
    componentEdge_isInvertible_iff Q a
  let m := cofiberTriangleMapOfHomotopy T D hT hD Q
  have h₁ : IsIso m.hom₁ :=
    (hc _).1 ((mem_weakEquivalences_iff_invertible h _).1 h₀)
  have h₃ : IsIso m.hom₃ :=
    (hc _).1 ((mem_weakEquivalences_iff_invertible h _).1 h₂)
  have hm : IsIso m.hom₂ := Pretriangulated.isIso₂_of_isIso₁₃ m
    (cofiberTriangle_mem_cofiberDistinguishedTriangles T hT)
    (cofiberTriangle_mem_cofiberDistinguishedTriangles D hD) h₁ h₃
  exact (mem_weakEquivalences_iff_invertible h _).2 ((hc _).2 hm)

end SerrePositivity.KST.Fibration
