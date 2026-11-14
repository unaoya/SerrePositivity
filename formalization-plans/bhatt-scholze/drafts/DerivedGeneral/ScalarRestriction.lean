-- 将来の置き場所：D 版は SerrePositivity.InfinityCategories.Derived.ScalarRestriction（仮。DerivedGeneral 2 本と同じ M13、`InfinityCategories/Derived/`、段 G・W2b 後）、
-- CAlg 版（`cAlgRestrictScalars` と忘却との比較）は EInfinity 側（M14 の隣、調整役）。11-03 に CAlg 版を追加（BS-D2 の指摘：A4 の塔は CAlg_A の中）。
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.1（Frobenius）、a4-design.md §2.1（塔 φ_{A*}^n、W9-II-01）。基準コミット efa846fe8。型検査対象（5∞-0）。
-- 2026-11-03（BS-D2 の質問への回答）：本体の `Derived/ScalarRestrictionNerve.lean` の `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数を制限する同型で、
-- D(T) → D(S) の関手ではない。必要なのは係数制限の ∞ 関手そのものなので、ここに基盤待ちの宣言として置く。
module

-- 取り込み時の依存先：drafts/DerivedGeneral/CompletionFunctor.lean（係数制限を用いない）。
public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BaseChange
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.ScalarRestrictionNerve
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity

/-!
# 係数制限の ∞ 関手 f_* : D(T) → D(S)（基盤待ち、M13）

## 概要
環準同型 f : S → T に沿う係数制限（忘却）の ∞ 関手 `derivedInfinityRestrictScalars f : derivedInfinityCategory T ⟶ derivedInfinityCategory S`。
既存の底変換 `derivedInfinityBaseChange f : D(S) ⟶ D(T)`（f^* = − ⊗^L_S T）の右随伴。

## 方針
dg 模型では T 複体を S 複体として読む忘却関手で、dg nerve との両立は本体 `dgNerveRestrictScalarsIso`（係数制限しても dg nerve は変わらない）。
∞ 関手としての構成と随伴は基盤側（M13、DerivedGeneral の完備化関手と同じ窓）。

## 規約
f は任意の環準同型。A0・A4 では f = φ_A（prism の Frobenius、一般には可逆でない）で φ_{A*} := `derivedInfinityRestrictScalars φ_A`。
塔 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯ は正の反復（W9-II-01。A 完全なら φ_{A*} ≃ (φ_A^{-1})^* だが、A0 の有界 prism では使わない）。

## 使われ方
A0 `prismaticCohomologyFrobenius`（Δ → φ_{A*}Δ、D 版）、A4 `frobeniusTower`・`prismaticPerfection`（CAlg 版と忘却の比較）、A5 の比較写像の脚 f_n = φ_B^{-n} ∘ f : Res_φ^n Δ_S → B。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.InfinityCategories

open SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.PerfectoidizationInterface (A_R)

variable {S T : Type u} [CommRing S] [CommRing T]
-- 11-03（BS-D2 の指摘）：f は型に現れないので section 変数にせず、各宣言の明示引数にする。

/-- 概要：f に沿う係数制限の ∞ 関手 f_* : D(T) → D(S)。
方針：dg 模型の忘却関手の dg nerve（`dgNerveRestrictScalarsIso` で係数制限は nerve を変えない）を D(T) → D(S) の射に。
規約：基盤待ち（M13）。f は明示引数。
使われ方：φ_{A*}。 -/
def derivedInfinityRestrictScalars (f : S →+* T) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory T ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S := E.restrictD f

/-- 概要：底変換と係数制限の随伴 f^* ⊣ f_*（Map(f^* X, Y) ≃ Map(X, f_* Y)）。
方針：dg 模型の tensor-hom 随伴を nerve に移す。単位と余単位を QCatAdjunction にまとめる。
規約：基盤待ち。
使われ方：φ_A 半線形な射 Δ → φ_{A*}Δ を f^*Δ → Δ と読み替える所（A4 の塔の余極限）。 -/
def derivedInfinityBaseChange_restrictScalars_adjunction (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) (derivedInfinityRestrictScalars (E := E) f) := by
  sorry -- M13：複体の係数拡大・制限の随伴を dg nerve に移す

/-- 概要：合成との両立：(g ∘ f)_* ≃ f_* ∘ g_*、id_* ≃ id（反復 φ_{A*}^n に使う）。
方針：忘却関手の合成。
規約：可逆な辺（`FunctorIso`）で述べる（頂点の等号ではない）。
使われ方：A4 `frobeniusTower` の φ_{A*}^n。 -/
def derivedInfinityRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedInfinityRestrictScalars (E := E) (g.comp f))
      (derivedInfinityRestrictScalars (E := E) g ≫ derivedInfinityRestrictScalars (E := E) f) := E.restrictD_comp f g

def derivedInfinityRestrictScalars_id : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedInfinityRestrictScalars (E := E) (RingHom.id S)) (𝟙 _) := E.restrictD_id S

/-! ## CAlg 版（A4 の塔は CAlg_A の中、D35）。置き場所は EInfinity 側（M14 の隣、調整役）。 -/

/-- 概要：f に沿う E∞ 代数の係数制限 f_* : CAlg(T) → CAlg(S)（T 代数を S 代数として読む）。
方針：EInfinityTheory の係数制限を用いる。
規約：基盤待ち（M13 の CAlg 版。置き場所は `EInfinity/`、調整役）。f は明示引数。
使われ方：A4 `frobeniusTower`（CAlg_A の図式 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯）、A5 の比較写像の脚。 -/
def cAlgRestrictScalars (f : S →+* T) : E.CAlg T ⟶ E.CAlg S := E.restrict f

/-- 概要：忘却との両立：U_S ∘ f_*^{CAlg} ≃ f_*^{D} ∘ U_T（`cAlgForgetDerived`）。
方針：どちらも台の複体の忘却。
規約：`FunctorIso`。
使われ方：A4 の塔の余極限を D(A) で計算してから CAlg に戻す所、Lemma 8.4 (a)。 -/
def cAlgRestrictScalars_forget (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgRestrictScalars (E := E) f ≫ E.forget S)
      (E.forget T ≫ derivedInfinityRestrictScalars (E := E) f) := E.restrict_forget f

/-- 概要：CAlg 版の合成・恒等との両立（D 版と同じ形）。 -/
def cAlgRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgRestrictScalars (E := E) (g.comp f)) (cAlgRestrictScalars (E := E) g ≫ cAlgRestrictScalars (E := E) f) := E.restrict_comp f g

def cAlgRestrictScalars_id : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgRestrictScalars (E := E) (RingHom.id S)) (𝟙 _) := E.restrict_id S

/-! ## CAlg の係数拡大（左随伴。11-03、BS-D3 停止点 2 の StrongDescent `prismScalarExtension` の一般形、D3-05） -/

/-- 概要：f に沿う E∞ 代数の係数拡大 f^! : CAlg(S) → CAlg(T)、X ↦ X ⊗^L_S T（`cAlgRestrictScalars f` の左随伴）。
方針：EInfinityTheory の底変換とその忘却比較を用いる。
規約：基盤待ち（M13 の CAlg 版、置き場所は EInfinity 側）。f は明示引数。
使われ方：A5 StrongDescent（A → C = A/(p, φ^{-1}(d)) に沿う Δ_T ⊗^L_A C）、A2 の底変換 (4)。 -/
def cAlgBaseChange (f : S →+* T) : E.CAlg S ⟶ E.CAlg T := E.baseChange f

/-- 概要：随伴 f^! ⊣ f_*（Map_{CAlg(T)}(X ⊗^L_S T, Y) ≃ Map_{CAlg(S)}(X, f_* Y)）。単位・余単位と三角恒等式をもつ。 -/
def cAlgBaseChange_restrictScalars_adjunction (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (cAlgBaseChange (E := E) f) (cAlgRestrictScalars (E := E) f) := E.baseChange_adjunction f

/-- 概要：忘却との両立：U_T ∘ f^! ≃ f^{*,D} ∘ U_S（`derivedInfinityBaseChange f`）。 -/
def cAlgBaseChange_forget (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgBaseChange (E := E) f ≫ E.forget T) (E.forget S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := E.baseChange_forget f

/-! ## 一般の補題（11-03、BS-D2 停止点 1 の A4 の「ScalarRestriction へ」三件の一般形） -/

/-- 概要：CAlg の係数制限は **sifted** 余極限錐を保つ（sifted 余極限は台の加群で計算され、加群の係数制限は全ての余極限を保つ）。
**任意の余極限では偽**（BS-D2 の D2-01、11-03）：空図式でも ℤ → F₂ に沿う制限は始対象を保たない（CAlg_{F₂} の始対象 F₂ の制限は CAlg_ℤ の始対象 ℤ ではない）。
一般に余積 ⊗_T は ⊗_S にならない。
方針：dg 模型で忘却は sifted 余極限を保つ；nerve に移す。
規約：基盤待ち。K は `IsSiftedInfinity`（F2/Presentable/SiftedInfinity）。A4 の塔（ℕ 添字、filtered）はこの場合。押し出しの保存は f が同型のときだけ
（A7：完全 prism の Frobenius。同型に沿う制限は同値）。
使われ方：A4 の塔の余極限、A7 の G-A7-4。 -/
theorem cAlgRestrictScalars_isColimitCone (f : S →+* T) {K : SSet.{u + 1}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity K] {F : K ⟶ E.CAlg T}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (cAlgRestrictScalars (E := E) f) c) := by
  sorry -- 基盤待ち：sifted 余極限は台で計算される

/-- 概要：f が環同型なら CAlg の係数制限は同値で、全ての余極限錐（押し出し・始対象を含む）を保つ。
方針：逆の制限と `cAlgRestrictScalars_comp`・`_id` で同値。
規約：基盤待ち。A7 の完全 prism の φ_A に使う。
使われ方：A7 `frobeniusColimit_relativeTensor`。 -/
theorem cAlgRestrictScalars_isColimitCone_of_bijective (f : S →+* T) (hf : Function.Bijective f)
    {K : SSet.{u + 1}} {F : K ⟶ E.CAlg T} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (cAlgRestrictScalars (E := E) f) c) := by
  sorry -- 基盤待ち
/-- 概要：D(−) の係数制限は**全ての**余極限錐を保つ（加群の忘却は左随伴 f^* と右随伴（余誘導）の両方をもつ）。CAlg 版と違い空図式・余積も保つ。 -/
theorem derivedInfinityRestrictScalars_isColimitCone (f : S →+* T) {K : SSet.{u + 1}} {F : K ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory T}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (derivedInfinityRestrictScalars (E := E) f) c) := by
  sorry -- 基盤待ち

/-- 概要：係数制限と導来完備化の両立：I ⊂ S、J ⊂ T で √(f(I)T) = √J なら、J 完備化の後に制限したものと、制限の後に I 完備化したものは `FunctorIso`
（導来完備性は根基だけによる。Koszul 完備化の塔は f で対応する）。
方針：D 版は DerivedGeneral/CompletionFunctor の `completion`（M13）で、CAlg 版は忘却との比較 `cAlgRestrictScalars_forget` を経由。
規約：基盤待ち。完備化の引数は有限な生成元の集合。A4 の `restrictFrobeniusCompletion`（f = φ_A、(p,d) と (p,φ(d)) は同じ根基）はこの特別な場合。
使われ方：A4 の Δ_perf の完備化と shift。 -/
def derivedInfinityRestrictScalars_completion (f : S →+* T) (I : Finset S) (J : Finset T)
    (h : (Ideal.span (f '' (I : Set S))).radical = (Ideal.span (J : Set T)).radical) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Derived.completion T J ≫ derivedInfinityRestrictScalars (E := E) f)
      (derivedInfinityRestrictScalars (E := E) f ≫ Derived.completion S I) := by
  sorry -- M13：Koszul 塔の係数制限と根基による完備化の不変性

/-- 零次環の台を界面の π₀ から取る。 -/
abbrev cAlgH0Ring (x : (E.CAlg S) _⦋0⦌) : Type u :=
  ((E.pi0 S).obj (SSet.HomotopyCategory.mk x)).right

instance (x : (E.CAlg S) _⦋0⦌) : Algebra S (cAlgH0Ring (E := E) x) :=
  ((E.pi0 S).obj (SSet.HomotopyCategory.mk x)).hom.hom.toAlgebra

/-- 概要：係数制限と H⁰：f_*(x) の H⁰ の台の環は x の H⁰ の台の環と同じで、S 作用は f に沿って読む。
方針：忘却は台の複体を変えない。
規約：基盤待ち。A4 の `restrictH0Equiv`・`restrictH0Equiv_base` はこれ（A4 の `cAlgH0Algebra` と同じ H⁰ の取り方）。
使われ方：Lemma 8.4 (b)、E3 の `h0`。 -/
def cAlgRestrictScalars_h0 (f : S →+* T) (x : (E.CAlg T) _⦋0⦌) :
    cAlgH0Ring (E := E) ((cAlgRestrictScalars (E := E) f).app _ x) ≃+* cAlgH0Ring (E := E) x :=
  ((Under.forget _).mapIso ((E.pi0_restrict f).app (SSet.HomotopyCategory.mk x))).commRingCatIsoToRingEquiv

theorem cAlgRestrictScalars_h0_base (f : S →+* T) (x : (E.CAlg T) _⦋0⦌) :
    (cAlgRestrictScalars_h0 (E := E) f x).toRingHom.comp
        (algebraMap S (cAlgH0Ring (E := E) ((cAlgRestrictScalars (E := E) f).app _ x))) =
      (algebraMap T (cAlgH0Ring (E := E) x)).comp f := by
  sorry -- E.pi0_restrict の成分の Under.w を取る


/-- 概要：離散代数の埋め込みと係数制限の両立（BS-D3 の D3-03、11-03）：離散 T 代数 U（`A_R T = Under (CommRingCat.of T)`）について、
U を f で S 代数として読んだものの埋め込み `algebraEmbedding S` の像と、U の埋め込み `algebraEmbedding T` の像を `cAlgRestrictScalars f` で制限したものは
`VertexIso`（E∞ 代数としては同じ離散環、係数だけ f に沿って読む）。
方針：`E.discrete_restrict` を当該頂点で評価する。
規約：基盤待ち。A5/PerfectSite の `discreteRestrictionIso`（f = φ_A）はこの特別な場合。
使われ方：A5 の比較写像の脚（完備な試験環の Frobenius の逆を読む所）、A4 の離散版との一致。 -/
def cAlgRestrictScalars_algebraEmbedding (f : S →+* T) (U : A_R T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((E.discrete S).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (CommRingCat.ofHom (U.hom.hom.comp f)))))
      ((cAlgRestrictScalars (E := E) f).app _ ((E.discrete T).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))) := (E.discrete_restrict f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)

end SerrePositivity.InfinityCategories
