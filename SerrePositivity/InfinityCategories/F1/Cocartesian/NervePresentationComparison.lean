module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StandardSimplexComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomOverNaturality

/-!
概要：底上の nerve 表示に沿い、元の全局所 native Hom 比較を移す。
方針：両側の直接制限で既存の局所比較を挟む。
規約：表示の同型を保持し、元の全局所 Hom を使う。
使われ方：標準単体の共有面に沿う比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (a : Over (nerve C)) (k : D ⥤ C) (e : a ≅ Over.mk (nerveMap k))
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の native Hom の表示に端点を揃えた、同じ局所比較。 -/
def cocartesianNerveNativeHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj
      ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj
        (Opposite.op (Over.mk (nerveMap k)))) ⟶
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom)) := by
  rw [← cocartesianBaseChangeHom_nativePresentation (nerveMap k) p q]
  exact cocartesianLocalHomComparison k p q

/-- 元の表示同型による同じ直接制限で移した全局所 Hom の分類比較。 -/
def cocartesianNervePresentationHomComparison :=
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).map e.inv.op ≫
    cocartesianNerveNativeHomComparison k p q ≫
      (intervalDiagramOverFunctor
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)).map (uliftOverMorphism e.hom).op

/-- 標準単体上では、構成済みの同じ比較そのものを回収する。 -/
lemma cocartesianStandardSimplexHomComparison_presentation {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ nerve C) :
    cocartesianStandardSimplexHomComparison σ p q =
      cocartesianNervePresentationHomComparison (Over.mk σ) (simplexNerveBaseFunctor σ)
        (simplexNerveOverIso σ) p q := by
  rw [cocartesianStandardSimplexHomComparison, cocartesianStandardSimplexSourceIso_hom,
    cocartesianStandardSimplexTargetIso_hom]
  rfl

/-- 関手の等式と同じ表示射で、比較写像自体が一致する。 -/
lemma cocartesianNervePresentationHomComparison_eq_of_eq
    {k' : D ⥤ C} (h : k = k') (e' : a ≅ Over.mk (nerveMap k'))
    (he : e.hom.left = e'.hom.left) :
    cocartesianNervePresentationHomComparison a k e p q =
      cocartesianNervePresentationHomComparison a k' e' p q := by
  subst k'
  have hi : e = e' := Iso.ext (Over.OverMorphism.ext he)
  subst e'
  rfl

end SerrePositivity.InfinityCategories
