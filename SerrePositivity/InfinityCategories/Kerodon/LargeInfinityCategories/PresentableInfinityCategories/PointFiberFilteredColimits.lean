module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointAccessibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessiblePullbackCompactCandidate

/-!
概要：固定標的の fiber の filtered 余極限と小さい compact 候補を構成する。
方針：任意の点射の filtered 保存を accessible cospan の構成へ渡す。
規約：点射の全小余極限保存や fiber の accessibility を仮定しない。
使われ方：固定始域 fiber の accessibility の生成部分を残した準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：κ-filtered 保存な同値持ち上げ射の固定標的 fiber は同じ余極限を持つ。
方針：点の filtered 余極限と点射の保存を引き戻しへ渡す。
規約：始域には同じ κ の余極限だけを要求する。
使われ方：固定始域 fiber の accessibility の存在部分。 -/
lemma fiber_hasSmallKappaFilteredColimits {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ E) (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (pullback p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_hasSmallKappaFilteredColimits p x hp hE
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.point_hasSmallColimits.hasSmallKappaFilteredColimits κ) hpc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointMap_isKappaAccessibleFunctor hκ x)

/-- 概要：固定標的 fiber の元の第一射影は同じ κ-filtered 余極限を保存する。
方針：点射の filtered 保存と引き戻しの成分判定を使う。
規約：標的の固定頂点は任意。
使われ方：fiber 内の compact 性の検出。 -/
lemma fiber_fst_isKappaAccessibleFunctor {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ E) (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (pullback.fst p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor p x hp hE
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.point_hasSmallColimits.hasSmallKappaFilteredColimits κ) hpc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointMap_isKappaAccessibleFunctor hκ x)

/-- 概要：accessible な同値持ち上げ射の固定標的 fiber に小さい compact 候補がある。
方針：点の accessibility と点射の filtered 保存を一般の候補構成へ渡す。
規約：filtered 生成性と fiber の accessibility はこの段階で結論しない。
使われ方：固定始域 fiber の filtered 生成表示へ接続する。 -/
lemma exists_accessibleFiber_compactCandidate
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    (p : E ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor p) (σ : Cardinal.{u}) :
    letI := hp.innerFibration
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback p x,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i ∧
          (∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up a))) ∧
          (∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p x (i.app _ (ULift.up a))) ∧
          ∀ z, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p x z →
            ∃ a : A _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z (i.app _ (ULift.up a))) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_accessiblePullback_compactCandidate hE _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.point_isPresentable.isAccessible hB
    p x hp hpc ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointMap_isKappaAccessibleFunctor Cardinal.isRegular_aleph0 x⟩ σ

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
