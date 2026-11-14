module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourcePresentable
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalReplacementReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalSaturatedClosure
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Presentable
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：presentable 圏の任意の小さい辺族について、局所対象への Bousfield 反射が存在する。
方針：固定始域射圏の終対象から得た実局所置換を N の反射構成へ渡す。
規約：局所置換・反射・局所対象の accessibility を追加仮定にしない。
使われ方：HTT 5.5.4.15(1)–(3)、強飽和性の同定への反射の供給。

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


/-- 各元の対象は、元の局所同値の辺によって局所対象へ置換できる。 -/
lemma exists_bousfieldLocalEquivalenceReplacement
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    ∃ (y : C _⦋0⦌) (e : Truncated.Edge (X := (truncation 2).obj C) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) y := by
  obtain ⟨y, e, he, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_bousfieldLocalReplacement hC edges x
  exact ⟨y, e.toTruncated,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.stronglySaturatedClosure_subset_localEquivalences (Set.range edges) hC.hasSmallColimits he, hy⟩

/-- 任意の小さい辺族の局所対象全部分圏は、元の presentable 圏の反射的部分圏である。 -/
@[kerodon 06VH]
lemma bousfield_isReflectiveSubcategory
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements (Set.range edges)
    (exists_bousfieldLocalEquivalenceReplacement hC edges)

/-- 公開された元の局所対象の定義を使う、coherent な Bousfield 反射の実データ。 -/
def bousfieldReflection
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges)) :=
  Classical.choice (bousfield_isReflectiveSubcategory hC edges)

/-- 選んだ反射の全関手を、元の局所対象全部分圏への局所化関手として公開する。 -/
def bousfieldLocalizationFunctor
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges := (bousfieldReflection hC edges).reflector

/-- 同じ元の局所対象全部分圏は、構成済みの反射を P-d の公開定理へ渡して presentable。 -/
@[kerodon 06VH]
lemma bousfieldLocalObjects_isPresentable
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_reflection hC edges (bousfield_isReflectiveSubcategory hC edges)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Lemma 5.5" (partial := direction) "仮定：表示可能準圏と、小さい辺族で強飽和生成された辺の類（原典の小生成からの向きと一致）。結論：元の局所対象圏は表示可能で、強飽和生成閉包に沿う反射が余極限を保ち、同じ辺の反転を表す（原典の小生成から局所化への向き）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable
attribute [cite HTT "5.5.4.15"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable
attribute [cite HTT "5.5.4.15"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection
