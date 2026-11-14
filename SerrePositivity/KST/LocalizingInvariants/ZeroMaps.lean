module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ZeroCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroDiagramComparison

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
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (SSet.const z : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout (SSet.const z : (Δ[1] : SSet.{u}) ⟶ X)
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, SSet.comp_const] using h

/-- 全対象を零対象へ送る実関手は完全。 -/
lemma isExact_of_zero_values {K X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (F : K ⟶ X) (hF : ∀ k, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F where
  preservesZero k _ := hF k
  preservesCofiber t _ := by
    let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X
    let G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X := SSet.const z.vertex
    have hG : ∀ k, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (G.app (Opposite.op ⦋0⦌) k) := by
      intro k
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
      exact z.isZero
    let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso G (t.square ≫ F) hG
      (fun k ↦ hF (t.square.app (Opposite.op ⦋0⦌) k))
    exact (constantSquare_isPushout z.vertex).of_functorIso e

/-- 零安定圏から指定安定圏への、選ばれた零対象を値とする完全関手。 -/
def fromZeroCategory (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} A where
  hom := SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).vertex
  isExact := isExact_of_zero_values _ (fun k ↦ by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex A.obj).isZero)

/-- 零角を経由した合成は、選ばれた零対象の定値関手そのもの。 -/
lemma throughZero_hom (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A).hom ≫ (fromZeroCategory B).hom =
      SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex B.obj).vertex := SSet.comp_const _ _

/-- 商による包含の零化は、零角を経由する関手との整合的な関手同型を与える。 -/
def verdierZeroCompositeIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.inclusion.hom ≫ d.projection.hom)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.left).hom ≫ (fromZeroCategory d.right).hom) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ d.isVerdier.kills_inclusion (fun k ↦ by
    rw [throughZero_hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex d.right.obj).isZero)

end SerrePositivity.KST.LocalizingInvariants
