module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallModelFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSpanCompactCardinals

/-!
概要：compact 対象を保つ cospan に小さい三成分模型と全自然な辺の比較を与える。
方針：各 compact 全部分圏の小さい模型を選び、制限関手を共役して降ろす。
規約：比較は元の全 compact 全部分圏を標的とし、頂点の代表選択だけで代用しない。
使われ方：引き戻し内の小さい compact 生成圏の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の compact cospan と全自然に比較される小さい cospan の模型。
方針：三つの全同値と二辺の関手同型を一緒に保持する。
規約：辺の比較の標的は元の compact 制限関手との合成。
使われ方：小さい引き戻しと元の compact 成分の引き戻しの接続。 -/
structure SmallCompactSpanModel (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (hp : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (hq : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y)) where
  left : SSet.{u}
  right : SSet.{u}
  base : SSet.{u}
  left_quasi : Quasicategory left
  right_quasi : Quasicategory right
  base_quasi : Quasicategory base
  left_equiv : letI := left_quasi
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj left)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ E)
  right_equiv : letI := right_quasi
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj right)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ D)
  base_equiv : letI := base_quasi
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj base)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ B)
  left_map : left ⟶ base
  right_map : right ⟶ base
  left_comparison : letI := left_quasi
    letI := base_quasi
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map left_map ≫ base_equiv.hom)
      (left_equiv.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ p hp)
  right_comparison : letI := right_quasi
    letI := base_quasi
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map right_map ≫ base_equiv.hom)
      (right_equiv.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ q hq)

/-- 概要：共通濃度で accessible な三圏の compact cospan は小さい模型を持つ。
方針：三つの小さい compact 模型を選び、共役関手とその余単位比較を取る。
規約：元の圏の厳密な小ささや引き戻しの accessibility を要求しない。
使われ方：presentable cospan の小さい compact 成分図式。 -/
lemma smallCompactSpanModel_nonempty {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (p : E ⟶ B) (q : D ⟶ B)
    (hp : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (hq : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y)) :
    Nonempty (SmallCompactSpanModel μ p q hp hq) := by
  obtain ⟨A, hA, ⟨a⟩⟩ := hE.exists_smallCompactModel
  obtain ⟨C, hC, ⟨c⟩⟩ := hD.exists_smallCompactModel
  obtain ⟨K, hK, ⟨k⟩⟩ := hB.exists_smallCompactModel
  have := hA
  have := hC
  have := hK
  exact ⟨{
    left := A
    right := C
    base := K
    left_quasi := hA
    right_quasi := hC
    base_quasi := hK
    left_equiv := a
    right_equiv := c
    base_equiv := k
    left_map := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor a k (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ p hp)
    right_map := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor c k (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ q hq)
    left_comparison := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor_comparison a k (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ p hp)
    right_comparison := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor_comparison c k (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ q hq) }⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
