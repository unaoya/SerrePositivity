module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFunctorRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCompactObjects
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexPullbackRestriction

/-!
概要：両成分が compact な引き戻しの全部分圏を、compact 成分圏の実引き戻しとして表す。
方針：元の引き戻しの頂点条件を両射影で制限する公開判定を適用する。
規約：元の全辺・全高次を保持し、元の引き戻し内での compact 性も供給する。
使われ方：小さい compact 候補圏と元の filtered 表示を接続する。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

variable (μ : Cardinal.{u}) {E D B : SSet.{u + 1}}
  [Quasicategory E] [Quasicategory D] [Quasicategory B] (p : E ⟶ B) (q : D ⟶ B)

/-- 概要：両射影が μ-compact となる元の引き戻しの頂点条件。
方針：元の二成分の compact 条件を合わせる。
規約：共通標的の像の compact 性は関手の保存性から別途得る。
使われ方：compact 生成候補の全部分圏の頂点。 -/
def ComponentCompactVertex (x : (pullback p q) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((pullback.fst p q).app _ x) ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((pullback.snd p q).app _ x)

/-- 概要：両成分が μ-compact な元の引き戻しの全部分圏。
方針：同じ頂点条件で元の全単体を制限する。
規約：元の二成分の全辺を保持する。
使われ方：引き戻しの compact 生成候補。 -/
def componentCompactObjects : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) (ComponentCompactVertex μ p q)

instance componentCompactObjects_quasicategory [InnerFibration p] :
    Quasicategory (componentCompactObjects μ p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：compact な第一成分への元の射影の制限。
方針：頂点条件の第一成分で全部分複体へ持ち上げる。
規約：元の第一射影そのものを保持する。
使われ方：compact 成分圏の引き戻し錐。 -/
def componentCompactFst : componentCompactObjects μ p q ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) (ComponentCompactVertex μ p q)).ι ≫ pullback.fst p q)
    (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x).1)

/-- 概要：compact な第二成分への元の射影の制限。
方針：頂点条件の第二成分で全部分複体へ持ち上げる。
規約：元の第二射影そのものを保持する。
使われ方：compact 成分圏の引き戻し錐。 -/
def componentCompactSnd : componentCompactObjects μ p q ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) (ComponentCompactVertex μ p q)).ι ≫ pullback.snd p q)
    (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x).2)

/-- 概要：compact 成分の全部分圏の正方形は元の実引き戻し。
方針：頂点条件が両射影から回収できる全部分制限の公開判定を使う。
規約：関手の compact 保存を明示し、生成性は仮定しない。
使われ方：compact 成分圏の小さい模型との比較。 -/
lemma componentCompactObjects_isPullback
    (hp : ∀ x : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (hq : ∀ y : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y)) :
    IsPullback (componentCompactFst μ p q) (componentCompactSnd μ p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ p hp) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction μ q hq) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isPullback_fullSubcomplex_restriction (IsPullback.of_hasPullback p q)
    (ComponentCompactVertex μ p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)
    _ _ _ _ rfl rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction_inclusion μ p hp)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactRestriction_inclusion μ q hq) (fun _ he hd ↦ ⟨he, hd⟩)

/-- 概要：両成分 compact な全部分候補圏の全対象は元の引き戻し内でも μ-compact。
方針：成分の compact 性と元の関手の像の compact 保存を全 Hom の判定へ渡す。
規約：元の引き戻しの accessibility は要求しない。
使われ方：小さい候補圏から元の compact 生成圏への接続。 -/
lemma componentCompactObjects_vertex_isKappaCompact
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) [InnerFibration p]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.fst p q))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.snd p q))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p)
    (himage : ∀ x : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (x : (componentCompactObjects μ p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x.val := by
  obtain ⟨he, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_pullback_of_components h p q hf hs hp x.val he hd (himage _ he)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
