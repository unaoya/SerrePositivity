# BS-M15（⑤d）作業報告 — G12 段 0（§71〜§74、2026-11-15）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## §71 BS-M15 §7 の受領：M15 は待機、G12 の段0へ（11-15）

ユーザー承認済みの §7 を main の文書で確認した。M15 は §67 の厳密ルートとし、
descendability の一般定義を保ち、示す適用を A5 の使用辺・図式に限る。
P0–P3 は A2（5∞-4）・A4（5∞-5）の出力であり、⑤d の構成対象から外す。
5∞-2 が形になるまで M15 の Lean 追加を止めたままにする。
§68 の M10 全族ルートは比較案の記録であり、以後の⑤dの実装方針にはしない。
検証済み16,936行の取り込みは調整役が行う。自枝から main へは書き込まない。

G12 の段0のため、⑤a worktree の report-codex-w16.md §60、§61.1–§61.2・§61.5 を読み直した。
厳密な bar 前段326行は既存の完成部品として再利用し、新しく作り直す見込みには入れない。
以下のG12一覧はM15の43項目とは別の初期一覧であり、法則の補題・証明分割を追加IDとして数えない。

M15：**一覧：済み 10／全体 43（うち追加 1）**。
G12：**一覧：済み 0／全体 15（うち追加 0）**。

## §72 G12 段0：同じ CAlg の native presentability

### 72.1 結論と厳密な目標型

**段0の見込みは追加6,900–12,700行、計画上の丸めで7,000–13,000行。**
上端13,000行は事前承認の5,000行を超えるため、§7の停止条件に従い**G12のLeanには着手しない**。
⑤a §61.5 の旧3,000–5,000行を、一般のモナド性が未供給のまま据え置かない。
外枠26,000行を自分で設定したことにはしない。上端を承認する場合の2倍の候補値である。

目標は既存の欄と同じ次の型である。

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

-- G15 の最終出力の型。未実装・紙のみ。
cAlg_isPresentable (A : Type u) [CommRing A] :
  @IsPresentable (barrattEcclesCore.CAlg A) (barrattEcclesCore.quasicategory A)
```

C := derivedInfinityCategory A、B := CAlg_R A、F := cAlgFreeDerived A、U := cAlgForgetDerived A と略記する。
B は別の代数模型に置き換えない。IsPresentable は現定義どおり IsAccessible B ∧ HasSmallColimits B。
後者は全 K : SSet.{u} と全 D : uliftFunctor.obj K ⟶ B の native な余極限の存在である。
普通の圏の locally presentable 性や、通常圏のfiltered保存だけをこの主張とは読まない。

### 72.2 再利用を確認した既存の部品

| 構成・命題 | 本体の宣言 | 今回の扱い |
|---|---|---|
| D(A) の同じ宇宙での presentability | HA/DerivedCategoryModels/DerivedCategories/DerivedCategory.lean:132 derivedInfinityCategory_isPresentable | 入力として再利用。再証明しない |
| 実導来自由・忘却随伴 | BarrattEccles/FreeProbeDerivedFreeForget.lean:36 cAlgFreeDerived、:39 cAlgFreeForgetDerivedAdjunction | 全単位・余単位を持つ既存 QCatAdjunction を使う |
| 同じ U の保守性 | Theory/Conservative.lean:133 cAlgForgetDerived_conservative | 元の可逆辺の反映を使う |
| 通常の自由・忘却随伴 | Operad.freeAlgebraAdjunction | 厳密な bar の再利用元 |
| 厳密な bar・同じ増大・追加退化 | StrictAdjunctionBar と Theory/StrictBar の strictBarFunctor、strictBarAugmentedFunctor、strictBarUnderlyingExtraDegeneracy | ⑤a §60で検収済みの326行を使う |
| 通常圏のモナド性 | EInfinity/Operad/AlgebraMonadic.lean | 通常圏の結果。native な∞モナド性の証明としては使わない |
| 通常圏の濃度・filtered保存 | Operad/AlgebraSmallObject の Algebra.forget_isCardinalAccessible、freeAlgebra_finitelyPresentable、AlgebraSiftedColimits.forget_createsSiftedColimitsOfShape | 濃度の候補・厳密な比較の材料に限定 |
| native accessibility・全小余極限の定義 | HTT/PresentableInfinityCategories/Definition.lean、Kerodon/…/CompactGenerationAndAccessibility/AccessibleFunctor.lean | 既存定義を固定する |
| 前層・Ind・小生成局所化のpresentability | Kerodon/…/PresentableInfinityCategories の既存群 | 適用仮定を個別に検査して再利用 |

⑤a旧 §61.2 の「誘導随伴の全単位・余単位が不足」という部分は、現在の上記宣言で解消されている。
一方、前層反射の IsPresentable.exists_presheafReflection は presentability を**仮定して**反射を出す向きである。
GeneratedSourcePresentable も ambient の IsPresentable を入力にする。これらに B 自身を代入して
B の presentability を証明する循環は作らない。

main 側にも同じ標的・随伴を確認した。InfinityCategories のモナド関連の既存 FreeComonad は
Dwyer–Kan の通常の相対圏の comonad であり、以下の native な Eilenberg–Moore 準圏の構成ではない。
現在確認した範囲には、これらの一般部品をそのまま埋める実装済みの native Barr–Beck と
accessible ∞ モナドの代数圏の presentability の公開宣言はない。
名前検索だけから不存在を数学的に主張するのではなく、使用可能な出力型としては未供給と扱う。

### 72.3 原典の対応と証明経路

[Higher Algebra](https://www.math.ias.edu/~lurie/papers/HA.pdf) の Proposition 4.7.3.3 と
Theorem 4.7.3.5 を再確認した。後者の適用には、左随伴の存在に加え、保守性と
U-split な単体図式の実現の存在・その保存が必要である。通常の追加退化の構成だけではこの条件を検収できない。
同書 Corollary 3.2.3.5 は代数∞圏のaccessibility・presentabilityの関連する一般結果であるが、
現在の BE 模型をその operadic な代数圏と全関手で比較する作業は別に必要である。
定義側は [Kerodon Definition 9.5.1.2, Tag 06ND](https://kerodon.net/tag/06ND) と
現行の HTT/PresentableInfinityCategories/Definition.lean に合わせる。

採用案は⑤a §61.2 のモナドの経路である。
既存の F⊣U から全 coherent な誘導モナドを構成し、その代数準圏との**同じU上の**比較を作る。
native な U-split 実現を検収して比較を同値とし、native accessibility と全小余極限を代数準圏で構成して B へ戻す。
最後の性質は同じCAlgの既存presentability欄の型で出す。

## §73 G12 の型つき初期一覧 G01–G15

以下は紙上の型の仕様。NativeMonad、MonadAlgebraInfinity、IsUSplit、NativeAugmentedBar は
**今後構成・定義する記号**であり、既存のLean名や仮定のinstanceではない。
NativeMonad C は Fun(C,C) の合成に対する associative ∞-代数としての全coherenceを持つ。
hFun(C,C) 上の通常の Monad を代用しない。MonadAlgebraInfinity T はその全coherentな作用の準圏。
IsUSplit U D は D≫U に同じ全増大と coherentな追加退化を与える分裂拡張の存在を表す。
単に各次数の切断やh上の等式を与える述語にはしない。

一般部分は InfinityCategories/ の HA 4.7・HTT 5.4/5.5 の対応する節、
BEへの適用は EInfinity/BarrattEccles/Presentable/ に置く予定。
Interface/・⑤aの既存bar・他レーンのファイルは変更しない。

### 73.1 全モナドと実際の代数準圏 G01–G03

```lean
-- C,E : SSet.{u+1}, [Quasicategory C], [Quasicategory E]
-- F₀ : C ⟶ E, U₀ : E ⟶ C, a : QCatAdjunction F₀ U₀

-- G01 HA 4.7.3.3：指定された同じ随伴からの全誘導モナド。
inducedNativeMonad a : NativeMonad C
FunctorIso (inducedNativeMonad a).endofunctor (F₀ ≫ U₀)
-- 単位・乗法は元の全単位・余単位に由来し、全coherenceも構成する。

-- G02 HA 4.7.2–4.7.3：同じモナドの全作用を持つ実代数準圏。
MonadAlgebraInfinity (T : NativeMonad C) : SSet.{u+1}
Quasicategory (MonadAlgebraInfinity T)
monadAlgebraForget T : MonadAlgebraInfinity T ⟶ C

-- G03 実自由代数関手と、同じ単位・作用を持つ随伴。
monadAlgebraFree T : C ⟶ MonadAlgebraInfinity T
QCatAdjunction (monadAlgebraFree T) (monadAlgebraForget T)
FunctorIso (monadAlgebraFree T ≫ monadAlgebraForget T) T.endofunctor
```

G02の宇宙が現行のu+1に収まることも検収する。大きな代数準圏を作ったことだけで、
元の欄の同じ宇宙でのpresentabilityに読み替えない。

### 73.2 元のbar・全分裂・U-split実現 G04–G06

```lean
-- G04 同じ随伴の全coherentな増大bar。対象に関しても全関手。
nativeBar a : E ⟶ NativeAugmentedBar E
-- nth value は (F₀ U₀)^(n+1)、増大は同じ counit。
-- BEでは strictBarAugmentedFunctor の像との全FunctorIsoを構成する。

-- G05 忘却後の同じbarの全分裂拡張。
∀ X : V E, IsUSplit U₀ ((nativeBar a).app _ X).underlying
-- 元の単位・余単位と一致する全追加退化・全増大の比較も出す。

-- G06 BEへの適用に必要な native な U-split実現の存在・保存。
∀ (D : nativeSimplicialShape ⟶ B), IsUSplit U D →
  ∃ c : JoinCocone D,
    IsColimitCone c ∧ IsColimitCone (mapJoinCocone U c)
```

nativeSimplicialShape は元の N(Δᵒᵖ) のu+1への指定持ち上げ。
G06は任意のnativeなU-split図式を量化し、厳密図式の像だけの主張で終えない。
③-bの3b-4の実現側R06–R10と③-aの図式の全比較は再利用候補だが、
厳密入力の実現と忘却の比較を受け取るだけなら、G06までにはさらに適用対象の表示の橋が要る。
現時点でその橋も供給済みとは数えない。G12で作ることになれば、ここにその費用を含む。
全 sifted 保存の完成欄を前提にしてG06を証明し、その結果から同じ欄を埋める循環は避ける。

### 73.3 native Barr–Beck と同じ比較の同値 G07–G09

```lean
-- G07 HA 4.7.3.4：元のUの作用からの指定比較。
monadicComparison a : E ⟶ MonadAlgebraInfinity (inducedNativeMonad a)
FunctorIso (monadicComparison a ≫ monadAlgebraForget _) U₀

-- G08 HA 4.7.3.5：同じ比較の実完全忠実性。
IsConservative U₀ → USplitRealizationCondition U₀ →
  IsFullyFaithful (monadicComparison a)

-- G09 同じ条件で実本質的全射性、したがって全準圏の同値。
IsConservative U₀ → USplitRealizationCondition U₀ →
  IsEssentiallySurjective (monadicComparison a)
-- 上の二本を用いて IsQCatEquivalence (monadicComparison a) を得る。
```

USplitRealizationConditionはG06と同じ形を一般E,U₀で定義した条件であり、
BEの適用では既存保守性とG06で証明する。結論を条件に埋め込むSetupにはしない。
G08–G09は全写像空間と実bar余錐で示し、h圏のモナド性だけでは終えない。

### 73.4 濃度・代数準圏のaccessibility・全小余極限 G10–G12

```lean
-- G10 普通のfiltered保存からnativeな保存へのBEでの全比較を構成する。
∃ κ : Cardinal.{u}, κ.IsRegular ∧
  IsKappaAccessibleFunctor κ U ∧
  IsKappaAccessibleFunctor κ (inducedNativeMonad (cAlgFreeForgetDerivedAdjunction A)).endofunctor

-- G11 accessible な実モナドの代数準圏のnative accessibility。
IsPresentable C → IsAccessibleFunctor T.endofunctor →
  IsAccessible (MonadAlgebraInfinity T)

-- G12 同じ代数準圏の任意の小さい全図式の余極限。
IsPresentable C → IsAccessibleFunctor T.endofunctor →
  ∀ (K : SSet.{u}) (D : SSet.uliftFunctor.obj K ⟶ MonadAlgebraInfinity T),
    ∃ c : JoinCocone D, IsColimitCone c
```

G10では元のcofibrant/diagram置換と濃度を比較し、ordinaryなAlgebra.forgetの
IsCardinalAccessibleをnativeなIsKappaAccessibleFunctorへ読み替えるだけの証明にはしない。
G11では元の小さい生成圏・Ind表示またはaccessible反射を構成する。
ordinaryな有限表示性をnative compact性と同一視しない。
G12は任意形状の余極限であり、Tが全余極限を保つと仮定しない。
これらは新たに構成する一般の出力で、IsAccessibleやHasSmallColimits自体を追加instanceにはしない。

### 73.5 同じCAlgへの移送と元の欄 G13–G15

```lean
-- G13 G09の同じ全同値に沿う移送。
cAlg_isAccessible (A : Type u) [CommRing A] : IsAccessible (CAlg_R A)

-- G14 同じCAlgに全小余極限を戻す。各図式の全余錐とその同型も保持。
cAlg_hasSmallColimits (A : Type u) [CommRing A] : HasSmallColimits (CAlg_R A)

-- G15 §72.1の元の欄を埋める。
cAlg_isPresentable (A : Type u) [CommRing A] :
  @IsPresentable (barrattEcclesCore.CAlg A) (barrattEcclesCore.quasicategory A)
```

CAlg_R と違うEM模型のpresentabilityだけを証明して完成としない。
同じUへのFunctorIso、元の単位・余単位・bar増大の比較はG01–G09の法則として検収する。
これら法則の証明分割は本一覧に新しいIDを加えず、型と200行超の証明の行数を報告する。

G12：**一覧：済み 0／全体 15（うち追加 0）**。

## §74 G12 の見込み・依存境界・段0の停止

### 74.1 再利用後の追加見込み

| 一覧の束 | 残る主作業 | 下端 | 上端 |
|---|---|---:|---:|
| G01–G03 | 全誘導モナドとEM準圏、同じ自由・忘却の全随伴 | 1,800 | 3,200 |
| G04–G06 | native bar・全分裂の比較とU-split実現の橋 | 1,400 | 2,600 |
| G07–G09 | canonical比較の全Hom・本質的全射性・同値 | 1,500 | 2,800 |
| G10–G12 | native濃度保存・EM accessibility・任意小余極限 | 1,800 | 3,300 |
| G13–G15 | 同じCAlgへU付きで移送、元の欄の検収 | 400 | 800 |
| **合計** | | **6,900** | **12,700** |

計画上は **7,000–13,000行**。これは空行・import・docstring・法則・証明分割を含む
新設Leanの見込みであり、M15の16,936行とは別枠で数える。
旧⑤a §61.5 の一般2,400–4,000＋適用600–1,000を、そのまま現在の完成上端とはしない。
既存になった導来随伴・保守性、厳密bar326行、通常代数のaccessibilityとモデル構造は再加算していない。
その一方で、全coherentなモナド作用とEM準圏、U-splitなnative実現の表示の橋、
同じCAlgでの濃度と全余極限の検収を未経験の一行の適用としては扱わない。
M15で起きた「通常構成の法則があるのでnativeな全比較も小さく済む」という外れ方を反映した幅である。
これは完成保証の上端ではなく、追加の一般結果が必要なら再評価すべき計画値である。

③-bからG06の全型がそのまま供給される場合、G04–G06のうちBE実現の費用を差し引ける。
ただし、その供給が現時点で検収できたとはしない。現在の③-bの報告ではTot側のR03d等も未完で、
実現側はその後である。供給予定の図式が厳密入力に限るか、任意のU-split native入力まで含むかを
型で確かめてから差し引く。一般モナド性とEMのpresentabilityを、③-bが作ると勝手に割り当てない。

### 74.2 模型からの直接経路の扱い

BEのmodelCategory、cofibrantly generated性、ordinaryな局所表示可能性・accessible置換は
実部品として再利用できる。しかし、それだけでHTT A.3.7.6の同じnative局所化の
presentabilityを証明したとはならない。必要な単体的／combinatorial表示と全局所化比較、
小さい生成関係を持つnative前層表示がまだ必要である。
現在のBousfield反射のAPIを使うにも、その同じnativeな小生成表示を先に作る必要がある。
本段0ではこの別経路を5,000行以内の既存の一行の適用として採用しない。
この経路の型・費用を別に承認なしで追加する実装も始めない。

### 74.3 停止と今回の差分

BS-M15 §7 の「段0の上端が5,000行を超えるなら止まって報告」に該当する。
したがってG12のLeanは未着手で止める。段0の停止であって、G12完成の停止点ではない。
P0–P3はA2/A4に残し、M15のLeanも5∞-2待ちのまま。

今回変更したのは本報告への紙の追記だけ。M15・G12のLean、drafts、Interface、
main、⑤a・③系のファイルは変更していない。ビルド・大きい監査・鍵の取得も行っていない。
紙の型はコンパイル済みと表示しない。G12の実装行数は0、M15検証済みの行数は16,936のまま。

G12：**一覧：済み 0／全体 15（うち追加 0）**。
M15：**一覧：済み 10／全体 43（うち追加 1）**。

