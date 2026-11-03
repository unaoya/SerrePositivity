-- 将来の置き場所：D 版は SerrePositivity.InfinityCategories.Derived.ScalarRestriction（仮。DerivedGeneral 2 本と同じ M13、`InfinityCategories/Derived/`、段 G・W2b 後）、
-- CAlg 版（`cAlgRestrictScalars` と忘却との比較）は EInfinity 側（M14 の隣、調整役）。11-03 に CAlg 版を追加（BS-D2 の指摘：A4 の塔は CAlg_A の中）。
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.1（Frobenius）、a4-design.md §2.1（塔 φ_{A*}^n、W9-II-01）。基準コミット 68ed1ec05。ビルドなし。
-- 2026-11-03（BS-D2 の質問への回答）：本体の `Derived/ScalarRestrictionNerve.lean` の `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数を制限する同型で、
-- D(T) → D(S) の関手ではない。必要なのは係数制限の ∞ 関手そのものなので、ここに基盤待ちの宣言として置く。
module

public import SerrePositivity.InfinityCategories.Derived.BaseChange
public import SerrePositivity.InfinityCategories.Derived.ScalarRestrictionNerve
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedInfinity
public import SerrePositivity.EInfinity.Perfectoidization.Comparison

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

namespace SerrePositivity.InfinityCategories

open SerrePositivity.EInfinity

variable {S T : Type u} [CommRing S] [CommRing T]
-- 11-03（BS-D2 の指摘）：f は型に現れないので section 変数にせず、各宣言の明示引数にする。

/-- 概要：f に沿う係数制限の ∞ 関手 f_* : D(T) → D(S)。
方針：dg 模型の忘却関手の dg nerve（`dgNerveRestrictScalarsIso` で係数制限は nerve を変えない）を D(T) → D(S) の射に。
規約：基盤待ち（M13）。f は明示引数。
使われ方：φ_{A*}。 -/
def derivedInfinityRestrictScalars (f : S →+* T) : derivedInfinityCategory T ⟶ derivedInfinityCategory S := sorry -- 基盤待ち（M13）

/-- 概要：底変換と係数制限の随伴 f^* ⊣ f_*（Map(f^* X, Y) ≃ Map(X, f_* Y)）。
方針：dg 模型の tensor-hom 随伴を nerve に移す。主張の形（∞ 随伴の述語）は基盤の名前が決まってから。
規約：基盤待ち。
使われ方：φ_A 半線形な射 Δ → φ_{A*}Δ を f^*Δ → Δ と読み替える所（A4 の塔の余極限）。 -/
theorem derivedInfinityBaseChange_restrictScalars_adjunction (f : S →+* T) : True := by trivial -- 基盤待ち（M13）

/-- 概要：合成との両立：(g ∘ f)_* ≃ f_* ∘ g_*、id_* ≃ id（反復 φ_{A*}^n に使う）。
方針：忘却関手の合成。
規約：可逆な辺（`FunctorIso`）で述べる（頂点の等号ではない）。
使われ方：A4 `frobeniusTower` の φ_{A*}^n。 -/
def derivedInfinityRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    FunctorIso (derivedInfinityRestrictScalars (g.comp f))
      (derivedInfinityRestrictScalars g ≫ derivedInfinityRestrictScalars f) := sorry -- 基盤待ち（M13）
def derivedInfinityRestrictScalars_id : FunctorIso (derivedInfinityRestrictScalars (RingHom.id S)) (𝟙 _) := sorry -- 基盤待ち（M13）

/-! ## CAlg 版（A4 の塔は CAlg_A の中、D35）。置き場所は EInfinity 側（M14 の隣、調整役）。 -/

/-- 概要：f に沿う E∞ 代数の係数制限 f_* : CAlg(T) → CAlg(S)（T 代数を S 代数として読む）。
方針：Barratt–Eccles 代数の忘却（作用素は同じ、係数だけ制限）の nerve。
規約：基盤待ち（M13 の CAlg 版。置き場所は `EInfinity/`、調整役）。f は明示引数。
使われ方：A4 `frobeniusTower`（CAlg_A の図式 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯）、A5 の比較写像の脚。 -/
def cAlgRestrictScalars (f : S →+* T) : CAlg_R T ⟶ CAlg_R S := sorry -- 基盤待ち

/-- 概要：忘却との両立：U_S ∘ f_*^{CAlg} ≃ f_*^{D} ∘ U_T（`cAlgForgetDerived`）。
方針：どちらも台の複体の忘却。
規約：`FunctorIso`。
使われ方：A4 の塔の余極限を D(A) で計算してから CAlg に戻す所、Lemma 8.4 (a)。 -/
def cAlgRestrictScalars_forget (f : S →+* T) :
    FunctorIso (cAlgRestrictScalars f ≫ cAlgForgetDerived S)
      (cAlgForgetDerived T ≫ derivedInfinityRestrictScalars f) := sorry -- 基盤待ち

/-- 概要：CAlg 版の合成・恒等との両立（D 版と同じ形）。 -/
def cAlgRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    FunctorIso (cAlgRestrictScalars (g.comp f)) (cAlgRestrictScalars g ≫ cAlgRestrictScalars f) := sorry -- 基盤待ち
def cAlgRestrictScalars_id : FunctorIso (cAlgRestrictScalars (RingHom.id S)) (𝟙 _) := sorry -- 基盤待ち

/-! ## 一般の補題（11-03、BS-D2 停止点 1 の A4 の「ScalarRestriction へ」三件の一般形） -/

/-- 概要：CAlg の係数制限は **sifted** 余極限錐を保つ（sifted 余極限は台の加群で計算され、加群の係数制限は全ての余極限を保つ）。
**任意の余極限では偽**（BS-D2 の D2-01、11-03）：空図式でも ℤ → F₂ に沿う制限は始対象を保たない（CAlg_{F₂} の始対象 F₂ の制限は CAlg_ℤ の始対象 ℤ ではない）。
一般に余積 ⊗_T は ⊗_S にならない。
方針：dg 模型で忘却は sifted 余極限を保つ；nerve に移す。
規約：基盤待ち。K は `IsSiftedInfinity`（F2/Presentable/SiftedInfinity）。A4 の塔（ℕ 添字、filtered）はこの場合。押し出しの保存は f が同型のときだけ
（A7：完全 prism の Frobenius。同型に沿う制限は同値）。
使われ方：A4 の塔の余極限、A7 の G-A7-4。 -/
theorem cAlgRestrictScalars_isColimitCone (f : S →+* T) {K : SSet.{u + 1}} [IsSiftedInfinity K] {F : K ⟶ CAlg_R T}
    (c : JoinCocone F) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (cAlgRestrictScalars f) c) := by
  sorry -- 基盤待ち：sifted 余極限は台で計算される

/-- 概要：f が環同型なら CAlg の係数制限は同値で、全ての余極限錐（押し出し・始対象を含む）を保つ。
方針：逆の制限と `cAlgRestrictScalars_comp`・`_id` で同値。
規約：基盤待ち。A7 の完全 prism の φ_A に使う。
使われ方：A7 `frobeniusColimit_relativeTensor`。 -/
theorem cAlgRestrictScalars_isColimitCone_of_bijective (f : S →+* T) (hf : Function.Bijective f)
    {K : SSet.{u + 1}} {F : K ⟶ CAlg_R T} (c : JoinCocone F) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (cAlgRestrictScalars f) c) := by
  sorry -- 基盤待ち
/-- 概要：D(−) の係数制限は**全ての**余極限錐を保つ（加群の忘却は左随伴 f^* と右随伴（余誘導）の両方をもつ）。CAlg 版と違い空図式・余積も保つ。 -/
theorem derivedInfinityRestrictScalars_isColimitCone (f : S →+* T) {K : SSet.{u + 1}} {F : K ⟶ derivedInfinityCategory T}
    (c : JoinCocone F) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (derivedInfinityRestrictScalars f) c) := by
  sorry -- 基盤待ち

/-- 概要：係数制限と導来完備化の両立：I ⊂ S、J ⊂ T で √(f(I)T) = √J なら、J 完備化の後に制限したものと、制限の後に I 完備化したものは `FunctorIso`
（導来完備性は根基だけによる。Koszul 完備化の塔は f で対応する）。
方針：D 版は DerivedGeneral/CompletionFunctor の `completion`（M13）で、CAlg 版は忘却との比較 `cAlgRestrictScalars_forget` を経由。
規約：基盤待ち。主張の形は `completion` の引数（イデアル）が確定してから。A4 の `restrictFrobeniusCompletion`（f = φ_A、(p,d) と (p,φ(d)) は同じ根基）はこの特別な場合。
使われ方：A4 の Δ_perf の完備化と shift。 -/
theorem derivedInfinityRestrictScalars_completion (f : S →+* T) : True := by trivial -- 基盤待ち（M13、`completion` の引数が決まってから型にする）

/-- 概要：係数制限と H⁰：f_*(x) の H⁰ の台の環は x の H⁰ の台の環と同じで、S 作用は f に沿って読む。
方針：忘却は台の複体を変えない。
規約：基盤待ち。A4 の `restrictH0Equiv`・`restrictH0Equiv_base` はこれ（A4 の `cAlgH0Algebra` と同じ H⁰ の取り方）。
使われ方：Lemma 8.4 (b)、E3 の `h0`。 -/
theorem cAlgRestrictScalars_h0 (f : S →+* T) : True := by trivial -- 基盤待ち（H⁰ の取り方 `cAlgH0Algebra`（A4）を基盤側に移してから型にする）

/-- 概要：離散代数の埋め込みと係数制限の両立（BS-D3 の D3-03、11-03）：離散 T 代数 U（`A_R T = Under (CommRingCat.of T)`）について、
U を f で S 代数として読んだものの埋め込み `algebraEmbedding S` の像と、U の埋め込み `algebraEmbedding T` の像を `cAlgRestrictScalars f` で制限したものは
`VertexIso`（E∞ 代数としては同じ離散環、係数だけ f に沿って読む）。
方針：`algebraEmbedding = discreteCAlgUnderEmbedding`（EInfinity/Perfectoidization/Comparison）の定義と忘却の比較 `cAlgRestrictScalars_forget`。
規約：基盤待ち。A5/PerfectSite の `discreteRestrictionIso`（f = φ_A）はこの特別な場合。
使われ方：A5 の比較写像の脚（完備な試験環の Frobenius の逆を読む所）、A4 の離散版との一致。 -/
def cAlgRestrictScalars_algebraEmbedding (f : S →+* T) (U : A_R T) :
    VertexIso ((algebraEmbedding S).app _ (nerveVertex (Under.mk (CommRingCat.ofHom (U.hom.hom.comp f)))))
      ((cAlgRestrictScalars f).app _ ((algebraEmbedding T).app _ (nerveVertex U))) := sorry -- 基盤待ち

end SerrePositivity.InfinityCategories
