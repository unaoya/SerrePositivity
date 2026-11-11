module
public import SerrePositivity.KST.SConstruction.DGKInputIdempotentComplete
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnconditionalStableCompactGeneration

/-!
概要：固定 dg 入力の元の ν 値を、同じ Indω の compact 生成界面へ接続する。
方針：元の ν の安定性と冪等完備性を、有限全存在を要しない Ind 正本の入口へ渡す。
規約：Ind の安定性に交換入力を追加せず、D-8 の κ-compact cone と同一視しない。
使われ方：K-7 d4 の元の包含・選択比較。構造射と全 dg 入力での照合は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective


local instance dgIndRegular : Fact (Cardinal.aleph0.{w}).IsRegular :=
  Cardinal.fact_isRegular_aleph0

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, v} R)

/-- 概要：同じ固定 ν 値の元の Indω を使う。
方針：Ind 正本に元の ν 値と ℵ₀ をそのまま渡す。
規約：反復 cone の非可算 κ とは区別する。
使われ方：K-7 d4 の compact 生成比較の標的。 -/
abbrev dgKInputIndCompletion := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity Cardinal.aleph0 (dgKInputStableValue R A).obj

/-- 概要：固定 ν 値は、同じ Indω の指定 compact 部分と同値。
方針：元の ν の冪等完備性を公開生成同値へ代入する。
規約：安定交換入力なしで構成し、順射は元の compact Yoneda とする。
使われ方：K-7 d4 の同じ元の入力と生成元の比較。 -/
def dgKInputCompactGenerationEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
        Cardinal.aleph0 (dgKInputIndCompletion R A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence Cardinal.aleph0 (dgKInputStableValue_isIdempotentComplete R A)

/-- 概要：同じ生成同値の順射は元の compact Yoneda そのもの。
方針：Ind 正本の順射の固定式を使う。
規約：別の包含を選ばない。
使われ方：選択比較の順方向を固定する。 -/
theorem dgKInputCompactGenerationEquivalence_hom :
    (dgKInputCompactGenerationEquivalence R A).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence_hom Cardinal.aleph0 _

/-- 概要：同じ compact 生成の包含後は元の全 Yoneda と厳密に一致。
方針：正本の包含式を元の ν 値へ代入する。
規約：対象別の同型へ弱めない。
使われ方：固定 ν と Ind の元の包含の全関手比較。 -/
theorem dgKInputCompactGenerationEquivalence_inclusion :
    (dgKInputCompactGenerationEquivalence R A).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R A) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence_inclusion Cardinal.aleph0 _

/-- 概要：同じ元の ν の全 Yoneda 像は指定添字宇宙で ℵ₀-compact。
方針：Ind 正本の Yoneda compact 性を適用する。
規約：D-8 の κ-compact 小 dg 模型の実供給とは区別する。
使われ方：元の入力を Indω の compact 生成元として読む。 -/
theorem dgKInputIndYoneda_isCompact (x : (dgKInputStableValue R A).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{max (u + 1) v, max (u + 1) v + 1} Cardinal.aleph0
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj).app
        (Opposite.op ⦋0⦌) (ULift.up x)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indYoneda_isKappaCompact Cardinal.aleph0 x

/-- 概要：元の Indω の compact 頂点は、同じ固定 ν の Yoneda 像に尽きる。
方針：固定 ν の冪等完備性を正本の本質像判定へ渡す。
規約：同じ元の Ind 頂点での頂点同型を保持する。
使われ方：K-7 d4 の compact 像の照合。 -/
theorem dgKInputInd_isCompact_iff_yoneda (x : (dgKInputIndCompletion R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{max (u + 1) v, max (u + 1) v + 1} Cardinal.aleph0 x ↔
      ∃ y : (dgKInputStableValue R A).obj _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj).app
          (Opposite.op ⦋0⦌) (ULift.up y)) x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_isKappaCompact_iff_yoneda Cardinal.aleph0 (dgKInputStableValue_isIdempotentComplete R A) x

/-- 概要：固定 ν の Indω は、元の compact 生成界面を追加の交換入力なしで持つ。
方針：交換を定理化した Ind 正本の最終公開入口へ同じ安定な ν 値を渡す。
規約：交換入力も有限全存在も追加仮定にしない。
使われ方：K-7 d4 の安定性・完全 Yoneda・元の全頂点の filtered 生成表示。 -/
def dgKInputStableCompactGeneration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StableCompactGeneration Cardinal.aleph0 (dgKInputStableValue R A).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_stableCompactGeneration_unconditional Cardinal.aleph0 le_rfl _
    (dgKInputStableValue_isIdempotentComplete R A)

/-- 概要：安定 compact 生成界面も同じ元の生成同値を保持する。
方針：最終公開入口が元の生成同値を保持する正本の厳密等式を使う。
規約：元の生成同値と包含を選び直さない。
使われ方：K-7 d4 の固定した包含と安定 Ind 界面の厳密照合。 -/
theorem dgKInputStableCompactGeneration_equivalence :
    (dgKInputStableCompactGeneration R A).equivalence =
      dgKInputCompactGenerationEquivalence R A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_stableCompactGeneration_unconditional_equivalence Cardinal.aleph0 le_rfl _
    (dgKInputStableValue_isIdempotentComplete R A)

/-- 概要：任意の compact 入力族に対し、同じ生成逆射と元の包含は全関手同型。
方針：正本の選択比較を同じ入力族へ前合成する。
規約：固定した ν 値の族であり、異なる dg 入力間の構造射自然性はまだ主張しない。
使われ方：K-7 d4 の選択比較を点別の選択へ弱めず保持する。 -/
def dgKInputCompactGeneration_familyIso {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects Cardinal.aleph0 (dgKInputIndCompletion R A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ (dgKInputCompactGenerationEquivalence R A).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj)
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationInverse_familyIso Cardinal.aleph0
    (dgKInputStableValue_isIdempotentComplete R A) a

/-- 概要：同じ順射を持つ任意の生成逆射も、全入力族上で公開逆射と比較できる。
方針：正本の逆同値選択比較を元の同じ族へ前合成する。
規約：順射は同じ compact Yoneda に厳密に固定する。
使われ方：K-7 d4 の生成同値の選択に依存しない包含比較。 -/
def dgKInputCompactGeneration_choiceFamilyIso
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgKInputStableValue R A).obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects Cardinal.aleph0 (dgKInputIndCompletion R A)))
    (he : e.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj)
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects Cardinal.aleph0 (dgKInputIndCompletion R A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ e.inv) (a ≫ (dgKInputCompactGenerationEquivalence R A).inv) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationInverse_choiceIso Cardinal.aleph0
    (dgKInputStableValue_isIdempotentComplete R A) e he).precomp a

end SerrePositivity.KST.NonConnective
