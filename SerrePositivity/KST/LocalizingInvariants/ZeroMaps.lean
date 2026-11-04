module

public import SerrePositivity.InfinityCategories.Stable.Exact.ZeroCategory
public import SerrePositivity.InfinityCategories.Stable.ColumnPushout
public import SerrePositivity.InfinityCategories.Stable.ZeroDiagramComparison

/-!
概要：零安定圏からの完全関手と、零値関手の完全性。
方針：定値四角形の普遍性と零値図式の関手同型を使う。
規約：自然性を頂点ごとの同型で置き換えない。使われ方：Verdier 列の零合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 定値四角形は退化した列四角形なので押し出し。 -/
lemma constantSquare_isPushout {X : SSet.{u}} [Quasicategory X] (z : X _⦋0⦌) :
    IsPushoutSquare (SSet.const z : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) := by
  have h := squareColumnDiagram_isPushout (SSet.const z : (Δ[1] : SSet.{u}) ⟶ X)
  simpa only [squareColumnDiagram, SSet.comp_const] using h

/-- 全対象を零対象へ送る実関手は完全。 -/
lemma isExact_of_zero_values {K X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
    (F : K ⟶ X) (hF : ∀ k, IsZeroVertex (F.app (Opposite.op ⦋0⦌) k)) :
    IsExactFunctor F where
  preservesZero k _ := hF k
  preservesCofiber t _ := by
    let z := chosenZeroVertex X
    let G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X := SSet.const z.vertex
    have hG : ∀ k, IsZeroVertex (G.app (Opposite.op ⦋0⦌) k) := by
      intro k
      rw [zeroDiagram_const_vertex]
      exact z.isZero
    let e := zeroDiagramFunctorIso G (t.square ≫ F) hG
      (fun k ↦ hF (t.square.app (Opposite.op ⦋0⦌) k))
    exact (constantSquare_isPushout z.vertex).of_functorIso e

/-- 零安定圏から指定安定圏への、選ばれた零対象を値とする完全関手。 -/
def fromZeroCategory (A : StableCategory.{u}) : ExactMap zeroCategory.{u} A where
  hom := SSet.const (chosenZeroVertex A.obj).vertex
  isExact := isExact_of_zero_values _ (fun k ↦ by
    rw [zeroDiagram_const_vertex]
    exact (chosenZeroVertex A.obj).isZero)

/-- 零角を経由した合成は、選ばれた零対象の定値関手そのもの。 -/
lemma throughZero_hom (A B : StableCategory.{u}) :
    (toZeroCategory A).hom ≫ (fromZeroCategory B).hom =
      SSet.const (chosenZeroVertex B.obj).vertex := SSet.comp_const _ _

/-- 商による包含の零化は、零角を経由する関手との整合的な関手同型を与える。 -/
def verdierZeroCompositeIso (d : VerdierSequence.{u}) :
    FunctorIso (d.inclusion.hom ≫ d.projection.hom)
      ((toZeroCategory d.left).hom ≫ (fromZeroCategory d.right).hom) :=
  zeroDiagramFunctorIso _ _ d.isVerdier.kills_inclusion (fun k ↦ by
    rw [throughZero_hom, zeroDiagram_const_vertex]
    exact (chosenZeroVertex d.right.obj).isZero)

end SerrePositivity.KST.LocalizingInvariants
