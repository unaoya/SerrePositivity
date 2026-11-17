# BS-W16 の報告（report-codex-w16.md） — ④ 段 0 の型案と D79 (i)(ii)（§61〜§82、2026-11-12〜11-13）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 61. ④の段 0：G12・M14・M15 の型案と実装の分割案（承認待ち）

### 61.1 現在の到達点と読み直した資料

§31 の下調べを、KL-W1 後の型・a 完了後の API に合わせて更新した。
読んだ入口は `EInfinity/Interface/Theory.lean`、`BarrattEccles/Theory.lean`、
`Theory/Assembly.lean`、`drafts/Shared/Descendable.lean` と HTT・HA の項目表。
項目表・drafts・界面は編集していない。この節の型案は紙上の案で、型検査済み宣言ではない。

今回使えるようになった a は、厳密な自由代数の指定 Hopf 比較の擬同型性を供給する。
一般の代数への実現による拡張、`forget_preservesSifted`、native な Tot の比較はまだ別の入力である。
G12・M14・M15 の証明でそれらを供給済みとは数えない。

### 61.2 G12：同じ CAlg の native presentability

入口の型案は既存の欄と完全に同じ。

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
-- 証明対象（紙の型案）
example (S : Type u) [CommRing S] :
    @IsPresentable (barrattEcclesCore.CAlg S)
      (barrattEcclesCore.quasicategory S) := by
  -- native accessibility と全小余極限を証明する
```

現在の `HTT/PresentableInfinityCategories/Definition.lean` の定義は
`IsAccessible C ∧ HasSmallColimits C`。§31 の旧名 `F2.Presentable` は使わない。
宇宙 u の全図式の native 余極限と、同じ CAlg の accessibility の両方が要る。

証明の筋は、D(S) 上の誘導された自由・忘却随伴を固定し、実際の BE 代数と
そのモナドの代数の全準圏比較を作り、accessible なモナドの代数の presentability を適用するもの。
`derivedInfinityCategory_isPresentable`、`Operad.freeAlgebraAdjunction`、
`Algebra.forget_isCardinalAccessible`、`freeAlgebra_finitelyPresentable` と
`AlgebraSiftedColimits.forget_createsSiftedColimitsOfShape` を再利用する。
`cAlgForgetDerived_conservative` と厳密な bar の分裂はモナド性の入力になる。
通常圏の filtered 保存を、局所化後の native な保存へそのまま読み替えない。

不足：誘導随伴の全単位・余単位、native な U-split 実現の比較、∞ モナド性、
accessible なモナドからの accessibility と全小余極限。
③-b の 3b-2／3b-4 が供給する一般の橋を検収してから、重複を差し引く。
HTT A.3.7.6 による模型からの直接経路は代替だが、現模型の単体的・組合せ的な仮定と
同じ native 局所化への比較の不足があるため、cofibrantly generated の事実だけでは採用しない。

地図：HA 3.2.3.5（直接の数学的対応）、HA 4.7.3.5（モナド性）、
HTT 5.5.1.1（presentability の特徴づけ）、HTT A.3.7.6（代替の模型表示）。
地図の項目名は照合したが、それらの一般定理が現在すべて証明済みだとはしない。

### 61.3 M14：同じ全自然変換としての P⁰

入口は `EInfinityTheory.powerOp0` の型を保つ。E を全欄の実例の引数とした紙の書き方では、
次の型と、その同じ α に関する四つの条件を一緒に供給する。

```lean
-- FunctorHom は Project/LocalizationAndKanExtensionAuxiliaries/FunctorCategories
(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] ⊢
  FunctorHom (E.forget k) (E.forget k ≫ E.restrictD (frobenius k p))
```

これは型の表示用で、E の既存の `powerOp0` を証明に使う循環にはしない。
実装では証明済み欄から固定した BE の `forget`・`restrictD` に対して α を構成し、
組み立て関数へ渡す。四条件の正確な型は `Theory.lean` の
`powerOp0_zero`・`powerOp0_pos`・`powerOp0_discrete`・`powerOp0_tot` をそのまま使う。
零次の式は `restrictD_homologyIso` と `pi0_forget` による同定の後で a ↦ a^p、
正のホモロジー次数の式は **H⁻ⁿ（n > 0）で零**。
離散と Tot は、同じ α の成分が指定 Frobenius の射に等しいという条件である。

証明の筋：BE の p 入力の係数解像度と作用から Frobenius 半線形な操作を構成し、
微分・符号・対称性を照合する。次に弱同値による局所化を通して coherent な全自然変換へ降ろし、
その変換の値を零次・負のコホモロジー次数・離散入力・Tot の順で計算する。
既存の `arityRepresentationChain`、BE の作用、係数制限の全関手とホモロジー比較を再利用する。
a の二色比較は指定射の管理に使えるが、p 入力の操作そのものの代用にはならない。

不足：p 入力の操作と微分の照合、半線形性、局所化での全自然性、四条件の同一変換での証明。
Tot の条件は G10 と係数制限との比較を待つ。
直接の出典の対応は §31 と同じ DAG XIII Construction 2.2.6・Remark 2.2.7。
HTT・HA の項目表にはこの操作の独立番号はなく、周辺の HA 3.1.3・3.2.3.1・4.7.3.5 の
完成を M14 の証明とは数えない。論文の再照合は実装前の紙の確認に含める。

### 61.4 M15：一般の E∞ 底を保った descendability

入口の型は drafts の既存 API と同じ二つを採用する。

```lean
(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(A : Type u) [CommRing A]
(R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) ⊢ Prop
-- IsDescendableOver (E := E) A R B f

(E : SerrePositivity.EInfinity.EInfinityTheory.{u})
(A : Type u) [CommRing A]
(R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) (n : ℕ) ⊢ Prop
-- HasDescentIndexLEOver (E := E) A R B f n
```

第一の定義は Mod_R(D(A)) で B の生成する thick ⊗-ideal が単位 R を含むこと。
第二は F := fib(f) として、指定された F^{⊗_R n} → R がその加群圏のホモトピー圏で零であること。
この指数の零射の条件は定義自体の数学的条件で、a の厳密な指定射の照合の弱化とは別である。

最初に閉じる定理の型案：

```lean
-- パラメータ E A R B f は上と同じ
IsDescendableOver (E := E) A R B f ↔
  ∃ n, HasDescentIndexLEOver (E := E) A R B f n
```

証明の筋と順序：

1. 一般の BE 代数 R の加群準圏を作り、安定性・相対テンソル・単位・底変換を構成する。
2. thick ⊗-ideal の生成と指数の有限性の同値を証明する。
   押し出しでの安定性は drafts の `isDescendableOver_pushout` と同じ型で供給する。
3. 指数の nilpotence から Amitsur の塔と Tot 降下を導き、
   `isDescendableOver_tot_equiv` の `AmitsurData` の同じ増大錐を扱う。
4. RHom の指数 ≤ 2、Frobenius 余極限の指数評価、完備版を一般の底のまま供給する。

不足は一般の R-加群の模型と native な比較、相対テンソルの全構造、
有限指数と厚い閉包の同値、Amitsur の塔の収束、完備化との整合。
通常の内部加群の余極限・balanced tensor と `StableVertexClosure` の retract・安定閉包は
再利用候補だが、全体を離散 A 上の D(A) に落として済ませない。
RHom と完備版にある `True := by trivial` は証明済み項目には数えず、
それぞれ一般 R 上の加群・指定射・完備化のデータを入れた主張へ置き換える設計を先に確定する。
M15 を `EInfinityTheory` の新しい欄として増やさない。

地図：HA 4.2.1.15、4.2.3.5・4.2.3.7、4.5.1.1・4.5.2.1・4.5.3.1 は
加群と相対テンソルの基盤。直接の descendability は Mathew Definition 3.18・Proposition 3.22、
指数の利用は BS17 §11.2・Lemma 11.22 に対応する（§31 の出典確認を引き継ぐ）。

### 61.5 規模・分担と停止点

③-b の橋と BE への適用の分担が未確定なので、一般部分と実例を含む幅を保つ。
以下は追加 Lean（空行・docstring 込み）の初期見込みで、証明済み行数ではない。

| 作業 | 内訳 | 見込み | 段 0 上端の二倍による停止基準 |
| --- | --- | ---: | ---: |
| G12 | 一般のモナド性・presentability 2,400〜4,000、BE 適用 600〜1,000 | 3,000〜5,000 | 10,000 |
| M14 | 操作と値 1,600〜2,800、局所化 600〜1,000、離散・Tot 600〜1,200 | 2,800〜5,000 | 10,000 |
| M15 | 一般 R-加群 2,500〜4,500、指数 900〜1,500、降下・評価・完備版 1,400〜2,500 | 4,800〜8,500 | 17,000 |
| **合計** | | **10,600〜18,500** | 各作業で判断 |

各作業の見込みの半分に達した段階で、止まらず実測と残りの見込みを報告する。
一般部分が他レーンから供給された場合は、適用の費用と重複しないよう再集計する。
G12 の最初の分担判断はモナド性と presentability の一般部分の担当、
M14 は p 入力の鎖レベル構成の経路の紙の確認、M15 は一般 R-加群の模型と比較の担当が必要。
RHom・完備版の正確な入力型は、M15 の実装前に利用側の A5 の担当とすり合わせる。
ここで未確定の `True` を実装可能な型として承認依頼するものではない。

**④の段 0 の停止点。承認を待つ。** 今回は紙の確認と報告だけで、Lean ソースの変更は零。
したがって新しい対象ビルド・監査・登録候補はない。共有鍵・整理券も取得していない。
3b-4 の BE 模型の実現・Tot・U の比較の担当は、§22 の 3 の判断を待つ。

## 62. M14 の紙の確認：出典の構成と D(k) の欄との比較が未供給

### 62.1 読んだ一次資料と構成経路

調整役の順序 M14 → M15 → G12 に従い、実装前に以下を確認した。

- [BS 著者版](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf) §8、特に Lemma 8.4、印刷 pp.63–64。
- [DAG XIII](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf) §2.2、特に Example 2.2.5、Construction 2.2.6、Remark 2.2.7、Warning 2.2.8、印刷 pp.34–35。

DAG の経路を模式的に書く。G = C_p、
T̂_p(M) = (M^{⊗p})^{tG}、T_p はその完全加群への制限からの余極限保存延長。
T_p はスペクトル的な k–k 双加群 B を用いて B ⊗_k (−) と表される。
標数 p の指定 Tate 類から右 k 加群の射 k → B[−1] を取り、
T_p → T̂_p、Tate の境界、ホモトピー軌道から対称冪への射、代数の作用を合成する。
得られる P⁰ は CAlg_k → Sp の全自然変換である。

Remark 2.2.7 はこの同じ構成の π₀ と正のホモトピー次数での値を計算する。
BS Lemma 8.4 はその消滅と、単体的余単体的 F_p 代数の levelwise Frobenius との比較を用いる。
通常の p 重積を全次数で直接 P⁰ とする構成ではない。

### 62.2 現在の欄までに足りない比較

現在の `EInfinityTheory.powerOp0` は

```lean
FunctorHom (forget k) (forget k ≫ restrictD (frobenius k p))
```

であり、成分は D(k) の射を与える。出典の Sp 値の変換をこの型へ持ち上げる比較は、
Construction 2.2.6 の結論そのものには含まれていない。
Warning 2.2.8 の通常の k 線形性への注意は、係数制限を入れる動機にはなるが、
それだけでスペクトル的な全自然変換の Frobenius 半線形な D(k) への持ち上げを証明しない。
§31・§61 では、この二段階を十分に分けずに「半線形な鎖レベル操作」と見積もっていた。

必要な主張を数学の型として固定すると、V_k : D(k) → Sp を Eilenberg–Mac Lane の忘却とし、
U_k : CAlg_k → D(k)、φ = Frobenius として次になる。

```text
α : NatTrans(U_k, φ_* U_k)
e : NatIso(V_k ◦ φ_*, V_k)
V_k(α) followed by e = P⁰_DAG
    in the functor infinity-category Fun(CAlg_k, Sp).
```

ここで射の向きは通常の数学の合成記法。必要なのは成分のホモロジーでの式だけでなく、
同じ全変換についての比較である。V_k の Lean の実装名とこの比較を先に設けるか、
BE の鎖の模型から α を独立に構成して同じ比較を証明する必要がある。
右 k 加群の射 k → B[−1] を、Frobenius でねじった左作用とも整合する双加群の射へ
持ち上げる条件を省略できない。左右作用のホモトピー群上の一致だけを証明して代用しない。

これは「現在の欄が不可能」という結論ではない。出典を読んで確認できたのは、
欄までの追加の持ち上げ定理が未供給であること。その定理の存在・構成経路をまだ確定していない。
特に k = F_p への特殊化だけで全自然性の持ち上げまで自動的に解消するとは扱わない。

### 62.3 実装に必要な部品と現在の不足

鎖の模型で進む候補は、G の周期的な完全解像度、ノルムと Tate 境界、
p 入力の BE 作用との比較、完全入力から全入力への延長、上記の持ち上げの順である。
既存の BE の対称群の射影解像度と作用は再利用できるが、
それらだけでは完全解像度・Tate 構成・指定類・双加群の左右作用を供給しない。
また T̂_p は一般の filtered 余極限を保存しないので、T_p との区別を保つ必要がある。

a で閉じた二色自由比較を p 入力の操作として流用しない。
ホモロジー群に Frobenius と零を次数ごとに指定し、それを coherent な自然変換とする実装も行わない。
実装する部品の型一覧は、上の持ち上げを鎖レベルでどう保証するかの確認後に確定する。
この不足を含めた行数を、既承認の 2,800〜5,000 行に収まると再断定する根拠はまだない。

### 62.4 判断を要する点と状態

まず、現在の D(k) 値の欄を維持したまま、§62.2 の持ち上げ定理の紙の確認を
M14 の最初の仕事として続ける方針の確認を求める。
出典が直接供給する Sp 値への変更は界面・利用側に影響するため、こちらでは行わない。
既存の界面を変更せず、持ち上げを仮定する補助構造体で欄を埋めることもしない。

今回の成果は実装前の紙の確認と、欠けていた主張の型の特定。
Lean ソースの変更・ビルド・監査・鍵の取得はなし。M15・G12・Tot の照合は未着手。
この型の判断がつくまで、M14 の構成を本体へ追加する作業は止める。

## 63. D79 候補：P⁰ の持ち上げと Sp 値への修正の比較（紙、判断待ち）

### 63.1 結論と二案の境界

提案は **案2（原典の Sp 値）を、まず k = F_p に限定して採用する**こと。
Lemma 8.4 の数学的な議論にはこれで足りる。現在の D(k) 値の欄を供給できたとは主張しない。
案1には、§62.2 の持ち上げ定理の存在を確定する課題が残る。
案2にも V と native なスペクトル圏、ホモトピー比較の実装が必要であり、界面の数行の変更だけでは済まない。
今回は比較の紙の作業だけ。界面・drafts・本体の Lean は変更しない。

出典は §62 の [BS 著者版 §8・Lemma 8.4](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf) と
[DAG XIII §2.2](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf)。
後者の Example 2.2.5 と Construction 2.2.6 の双加群・指定類による経路を基準とする。

### 63.2 V_k の供給状況と作る経路

本体で確認した範囲：

| 部品 | 読んだ所在 | 供給と限界 |
| --- | --- | --- |
| 対称スペクトル、安定局所化 | `Spectra/Stable/LocalizingMaps`・`Replacement`・`EnrichedModel`・`DerivedTensorInverse` | 安定化・局所化の材料。一般の基礎模型や presentation を引数とする宣言もある。D(k) → Sp の完成した全関手ではない |
| Ω スペクトルと写像空間 | `KST/Spectra.lean` と `KST/Spectra/` | `OmegaSpectrum`、ループ・写像・ホモトピー群の基盤。これを本件の native Sp と同定し、D(k) の全関手へ接続する工程は別 |
| 安定準圏の一般論 | `InfinityCategories/HA/StableInfinityCategories/` | suspension・loop・exact functor・三角構造。安定性だけから D(k) の Eilenberg–Mac Lane 関手の実例は得られない |
| 加群の Dold–Kan | `Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/DoldKanIso` | `standardDoldKanModuleIso` は dg Hom の標準模型と Mathlib Γ の同型。対象の非有界複体全体のスペクトル化とは別 |
| D(k) のホモロジー・安定性 | `Project/DerivedCategories/Homology`・`ModulePiZeroMoore`・`StableHomotopyComparison` | `derivedInfinityHomologyFunctor`、`modulePiZeroMooreEquiv`、`derivedStableHomotopyEquivalence` 等。ホモトピー圏の比較を native な V と取り違えない |

以上と `Eilenberg`・`DoldKan`・spectrum 関連の宣言検索では、
**要求された V_k と自然な π_n V_k ≅ H^{-n} の比較を一式で使える入口は確認できなかった**。
名前の検索だけを数学的な不存在の証明とはしない。

構成案：複体を加法群へ忘却し、各整数シフトの適切な connective truncation に Γ を適用する。
標準ループ比較を指定して Eilenberg–Mac Lane の Ω スペクトルを作る。
全鎖写像・パラメータ付き写像への自然性、準同型を安定同値へ送ることを示し、
現在の `derivedInfinityCategory k` の局所化を通して native V_k を得る。
必要なのは対象ごとのスペクトルだけでなく全関手、自然な整数次数の π/H 比較、
極限・幾何学的実現との比較、係数を忘れる比較である。

一般の係数制限について V_S ◦ f_* ≃ V_T を持てば、案1の e にも利用できる。
案2を F_p のみで始める場合は V_{F_p} を先に作り、全 k の係数比較は後へ送れる。
`[ModelCategory SSet]` を自由な仮定として置く宣言をそのまま適用したことにはしない。
スペクトルの模型の選択と、既存 KST の Ω スペクトルへの比較の要否を、着手前に調整役と確定する必要がある。

### 63.3 案1：Frobenius 半線形な D(k) への持ち上げ

固定する数学的な型は §62.2 と同じ。

```text
U_k : CAlg_k → D(k),  V_k : D(k) → Sp,  φ = Frob_k
α : NatTrans(U_k, φ_* U_k)
e : NatIso(V_k ◦ φ_*, V_k)
e ◦ V_k(α) = P⁰_DAG  in Fun(CAlg_k, Sp).
```

候補経路は、DAG の B に対し指定 Tate 類の右 k 加群射を、
左作用を φ でねじった双加群の射へ持ち上げ、その射を全入力とテンソルして α を作るもの。
その後 Tate 境界・BE の p 入力作用との比較を全自然変換として示す。
B の両作用のホモトピー群での照合と、双加群射の存在・coherence は分けて証明する。

現時点でその双加群の持ち上げの存在を保証する既存宣言・出典の定理は特定していない。
Warning 2.2.8 が通常の k 線形性を否定することは、Frobenius twist 後の持ち上げの
存在も不存在も決めない。k = F_p でも coherent な持ち上げが自動的にあると仮定しない。
したがって案1の総規模には、存在自体の紙の確認という未評価のリスクがある。

この持ち上げが存在し、原典の P⁰ と同一と証明できれば、Lemma 8.4 は通る。
その際の消滅の論証自体は Sp へ忘却してよく、D(k) の射としての強さを本質的には使わない。

### 63.4 案2：Sp 値の界面と A4 の必要条件

Sp を native 準圏として固定し、W_k := U_k ⋙ V_k（Lean の合成順）とする案。
型の模式図であり、未実装の Sp を既存の宣言名として扱わない。

```text
powerOp0Sp : FunctorHom W_k W_k
π_n : h Sp → AddCommGrp
π_n V_k(x) ≅ underlyingAddGroup(H^{-n}(x))   -- x と射に自然
powerOp0_zero : π_0(powerOp0Sp_X) = Frobenius  -- π_0 U と環の比較後
powerOp0_pos  : ∀ n > 0, π_n(powerOp0Sp_X) = 0
```

離散・Tot の欄は D(k) の射の等式から h Sp の射の等式へ移す。
両辺は同じ W_k で忘却し、指定 Frobenius の像と比較する。
P⁰ を環スペクトルの射や CAlg の辺として要求しない。
π₀ の環構造は U_k の π₀ の環から比較で運ぶもので、Sp の全対象に環構造を置かない。

A4 の依存の洗い出し：

| 箇所 | 現在の D(k) 依存 | Sp 案の扱い |
| --- | --- | --- |
| `Shared/EInfinityPowerOperation.powerOperationZero` | `cohomologyOnHo.map` と `restrictD_homology` により成分を読む | π_n の写像を π/H の自然同型で共役する |
| 同 `powerOperationZero_natTrans`・`primeField` | D(k) 内の半線形変換、係数制限の恒等比較 | W_{F_p} 上の自己変換。係数 twist の消去は不要 |
| 同 `powerOperationZero_component` | D(k) のホモトピー圏の射を辺に持ち上げる | Sp の成分と π/H 比較の自然性へ書き換える。D(k) の辺を選ぶ必要はない |
| 同 `eq_frobenius_discrete`・`eq_frobenius_tot` | 等式の終域が h D(k) | 指定 Frobenius の像との h Sp の等式へ変更 |
| `A4/Perfectoidization.prismaticPerfection_coconnective` | 結論は D(A) の coconnectivity。現在の証明は sorry と説明コメント | mod p の対象を CAlg_{F_p} へ制限し W_{F_p} で読む。π_n の消滅を π/H 比較で H^{-n} の消滅へ戻す |
| 同 `prismaticPerfection_h0_perfectDelta` | H⁰ 上の Frobenius、C/p ↪ H⁰(X/p) の単射 | π₀/H⁰ の環と射の比較で足りる。P⁰ 自身を D(A) の射とする必要はない |
| 同 `perfectoidization_coconnective` | d の正則性と完備性の議論 | 上の二結果から進み、P⁰ の線形な持ち上げを使わない |

したがって **数学の筋は Sp 案で通るが、現在の Shared の定義を無変更で再利用はできない**。
A4 の結論の型を変える必要はなく、共有の操作の読み方を変える必要がある。

必要な橋を明記する。mod p の対象 X を CAlg_{F_p} に移し、塔の shift の像が
P⁰ の同じ成分に一致することを、A2 の levelwise Frobenius 比較から得る。
W_{F_p} の必要な極限と幾何学的実現の保存・比較、変換と指定錐の両立を用いる。
shift が同値なら π_n(P⁰) は同型で、n > 0 では同時に零なので π_n W(X) = 0。
π/H 比較から X/p の coconnectivity、p 完備性と導来 Nakayama から X の結論へ進む。
P⁰ と shift の可換性だけでは、P⁰ の可逆性は導けない。

### 63.5 k = F_p に限定する範囲

**Lemma 8.4 と G-A4-1 には F_p で足りる。** 元の底 A/p 自体を F_p と同一視せず、
標準写像 F_p → A/p に沿う CAlg の係数制限を用いる。
Frobenius は F_p を固定するので、制限後には自己変換と shift の比較を述べられる。
H⁰ の Frobenius は、任意の F_p 代数の台の環で x ↦ x^p と主張できる。
一般の k の P⁰ を構成したとみなさず、最初の欄を p と CAlg_{ZMod p} に絞る案を推す。
一般 k の操作が必要になれば、CAlg_k → CAlg_{F_p} と V の係数忘却比較により
Sp 値の操作を移す経路を別途供給する。

### 63.6 規模の比較と判断点

以下はソースの調査からの初期見込み。全関手・自然性・同じ指定射の照合を含める。
未知の一般構成が多く、既承認の M14 2,800〜5,000 行を確定した上限として流用しない。

| 部品 | 追加 Lean の見込み |
| --- | ---: |
| native Sp の入口・既存 Ω 模型との接続の必要部分 | 1,500〜3,000 |
| V_{F_p}、π/H の全自然比較、局所化、必要な極限・実現比較 | 2,000〜4,000 |
| P⁰ の Tate・p 入力・指定類・全自然変換と次数の計算 | 3,000〜5,500 |
| 離散・Tot・実現の同じ変換の照合と Shared/A4 移行 | 1,000〜2,000 |
| **案2の F_p 最小範囲** | **7,500〜14,500** |
| 一般 k の V と係数忘却の比較（必要な場合の追加） | 700〜1,500 |
| 案1の半線形双加群の持ち上げと原典との全比較（存在が確定した場合のみの追加） | 1,500〜3,500 |

案1は共通の Sp 経路と一般 k の比較も含めて **条件付き 9,700〜19,500 行**。
持ち上げの存在を紙で確定できない限り、これは完成の保証や費用の上界ではない。
案2にはその存在問題がなく、Lemma 8.4 の所要の強さに一致するため優先する。
新しい規模は新しい作業案であり、これを自己承認の実装枠にしない。
スペクトル側を他レーンが供給する場合は該当部分を差し引き、同じ行数を二重計上しない。

判断してほしい点：案2・F_p 最小範囲の採用、native Sp の模型の選択と V の担当、
界面と Shared の移行範囲。3b-2／3b-4 の担当決定と、極限・実現比較の費用を合わせる必要がある。
**ここで紙の比較の停止点として止め、D79 の決定を待つ。**
Lean の変更・ビルド・監査・鍵の取得はなし。M15・G12 へは進まない。

## 64. D79 (i) の実装とスペクトル模型の最初の区切り（検証済み）

main の §24・D79 を取り込み、界面・組み立て関数・Shared・A4 の型を変更した。
`[CharP k p]` を保つ。全界面の `toSpectra k` とその比較はデータとして受け取り、
実例の証明は指示どおり F_p から構成する。一般 k の実例を今回供給した意味ではない。

### 64.1 使う実在の Sp と π

追加調査で `KST/Spectra/CoherentNerve.lean` の `KST.Spectra.Sp` と
`KST/LocalizingInvariants/SpectrumHomotopyFunctor.lean` の
`SpectrumHo.piFunctor : ℤ → (hoFunctor.obj Sp ⥤ CommGrpCat)` を確認した。
Sp は既存 Ω スペクトルの単体的圏の coherent nerve で、quasicategory の実例も既存。
π は任意の辺の類から BF 射の代表を回収し、代表の選択に依存しない実際のホモトピー群関手。
`CommGrpCat.toAddCommGrp` で加法記法へ送って使う。
§63 の調査ではこの native Sp と π の入口を特定しきれていなかったため、この点を訂正する。
V と自然な π/H の比較の入口は引き続き新しく作る必要がある。

当面この Ω 模型を標的に固定する。`Spectra/` の対称スペクトルとの新しい比較同値は要求せず、
両模型を同一と仮定もしない。追加の `[ModelCategory SSet]` を仮定する経路は使わない。
界面は既存の Sp のみを参照し、BE 模型の定義を参照しない。

### 64.2 新しい欄と指定射

- `toSpectra S : D(S) ⟶ KST.Spectra.Sp`。
- `toSpectra_homologyIso S i`：hV の後の実 π_{−i}（加法化）と Hⁱ の台の加法群の自然同型。
- `toSpectra_restrict f`：係数制限後に忘れた Sp と元の Sp の全関手の同型。
- `powerOp0`：`forget k ≫ toSpectra k` の coherent な自然自己変換。
- `powerOp0_zero`・`powerOp0_pos`：同じ Sp の成分への π₀ と πₙ（n > 0）の主張。
- 離散・Tot：従来の指定 Frobenius の D(k) の射を hV で送り、
  `toSpectra_restrict` で台のスペクトルへ戻した同じ射との等式。

最初の型検査で、最後の係数忘却比較を省くと右辺が V(φ_*X) に着地し、
P⁰ の自己射と終域が合わないことを確認した。この比較を明示して再検証し、対象ビルドを通した。
P⁰ の D(k) への持ち上げは要求しない。

組み立て関数には V と二つの比較を未供給引数として追加。
`drafts/Shared/BarrattEcclesTheory` も同じ引数を受ける。
Shared の操作は Sp の π を π/H の同型で共役して読み、D(k) の辺を選ばない。
A4 の coconnectivity の結論は変更せず、その証明の筋を Sp と π/H の比較に合わせた。
実現・Tot の比較を証明済みとする変更は加えていない。

### 64.3 検証の状態

対象は `Interface.Theory` と直接の importer `BarrattEccles.Theory.Assembly`。
ビルドの整理券は一枚、`--wait 3600`。新しい実例の証明はまだない。
成功・公理監査の結果を回収してから、(i) の変更をコミットして報告する。
Shared と A4 は drafts の規則どおりビルド対象に入れない。
次の (ii) は、この同じ Sp を標的とする V_{F_p} と π/H 比較の構成である。


### 64.4 先行取り込み用の検証結果

対象 `BarrattEccles.Theory.Assembly` と依存する `Interface.Theory` は
`/tmp/bsw16/d79-interface-02.log` でビルド成功（12,922 jobs）。
変更した本体二本を `/tmp/bsw16/audit-d79.lean` で監査し、
**104 宣言、標準三公理のみ**で成功。ログは `/tmp/bsw16/audit-d79.log`。
本体に sorry・追加公理はない。Fully qualified な長い行に longLine の style 警告が残る。
監査とビルドは別の鍵で行い、それぞれ終了を回収して鍵と整理券を返却した。

取り込み対象は本体二本、drafts 三本、報告書。
新規モジュールはないため、共通入口・共通監査への追加登録は不要。
Shared の二つの数学的性質（零次 Frobenius、正のホモトピー次数で零）と
離散・Tot との比較は保ち、それを読む型だけを Sp と π/H へ移した。
drafts の sorry を新しい証明として数えていない。

(i) の先行取り込みが可能な区切りまで完了。
(ii) では既存 Ω 模型の Sp を標的に、V_{F_p} とその π/H の自然比較を構成する。
一般 k の V と係数忘却の実例、P⁰ 自体と Rem 2.2.7、離散・Tot の照合は未供給。
新しい構造欄を証明済みの実例として埋めた、という報告ではない。

### 64.5 夜の取り込み点

**取り込み点：D79 (i)、`615ceab26`。** 界面と drafts の型変更は先行して取り込める。
朝の調整役の取り込みを待たず (ii) へ進む。承認が要る変更や上限の見込みに当たった場合は、
その線の Lean を止めて M15 の一般 R 加群の紙の段 0 へ移る。

## 65. D79 (ii)：同じ Γ による各段からの構成（進行中）

模型選択は §64.1 のとおり既存の Ω スペクトルの native Sp。
Γ(M[n] の非正 smart 切断) を第 n 段に取る。
この符号なら、第 n 段の π_{j+n} は H^{-j}(M) に対応する。
Γ から得た段に suspension 構造射を入れ、随伴構造射の全基点での π 同型を示す。
Γ の段を持つだけでは `OmegaSpectrum` の `sigma_mono` は自動的には得られないため、
まず `KanSequence` の Ω 条件を示し、既存 `KanSequence.cofibrantOmegaSpectrum` へ進む。
同じ置換の自然性・単体的パラメータへの整合を確認してから native 関手へ降ろす。
置換の対象ごとの存在だけで全関手を作ったことにはしない。

最初の追加モジュールは `PowerOperation/EilenbergMacLaneLevels`。
シフト・smart 切断・Γ の実関手と、同じ Γ の正規化が指定切断へ戻る自然同型を供給する。
ここでは構造射・Ω 条件・V 自体の完成を主張しない。対象ビルドは未回収。

### 65.1 各段・基点・Kan 性の最初の検証済み束

`PowerOperation/` の三本を対象ビルドと監査に通した。

| モジュール | 行数 | 供給 |
| --- | ---: | --- |
| EilenbergMacLaneLevels | 50 | 実シフト・smart 切断・Γ の全関手、同じ Dold–Kan の余単位による正規化の自然同型 |
| EilenbergMacLanePoints | 42 | 単体的加群の零基点を全次数・全射で保持する関手、台の段との一致 |
| EilenbergMacLaneKan | 39 | 単位からの dg Hom の実 Γ との同型、既存 N4 の線形充填からの Kan 性 |
| **計** | **131** | |

ビルド `/tmp/bsw16/em-levels-03.log` は成功（3,784 jobs）、新規警告なし。
監査 `/tmp/bsw16/audit-em-levels.log` は **三本・29 宣言・標準三公理のみ**。
本体に sorry・追加公理なし。終了を回収し、鍵と整理券を返却済み。
新規登録候補はこの三本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
共通入口・共通監査は変更しない。

ここで止まらず、π と正規化ホモロジーの既存の一般比較を各段へ接続する。
構造射・Ω 条件・単射化の全関手性・局所化と native V はまだ未供給。

### 65.2 指定された各段の π/H と自然性

さらに四本を検証した。全て `EInfinity/PowerOperation/` 以下。

| モジュール | 行数 | 供給 |
| --- | ---: | --- |
| EilenbergMacLaneStageHomology | 54 | Γ の正規化のホモロジーの自然同型と、零基点の正次数 π/Moore 比較 |
| EilenbergMacLaneStageNaturality | 44 | 同じ各段の比較が任意の鎖写像で可換する式 |
| EilenbergMacLaneTruncation | 44 | smart 切断の H_d を H^{-d} へ、シフトした段を H^{r-d} へ戻す同型。d=0 の境界も含む |
| EilenbergMacLaneCohomotopy | 46 | 各段の π_{n+1} と H^{r-(n+1)} の群同型、n+1=j+r の場合の H^{-j} への移送 |
| **追加計** | **188** | |

最終ビルドは `/tmp/bsw16/em-stages-final.log`、監査は
`/tmp/bsw16/audit-em-stages.log`。七本計 **73 宣言・標準三公理のみ**で成功。
七本の実測は **319 行**、新規警告・sorry・追加公理なし。
構造射を仮定に加えた V の実例を作ったのではなく、実際の指定 Γ の各段について証明したもの。
零次数の段の π₀、構造射、Ω 条件、置換の全自然性、native V は未供給。
特に各段の群同型を持つことだけから、スペクトル全体の全自然比較の完成とは扱わない。

登録候補は今回の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
§65.1 と合わせ七本。共通入口と共通監査は調整役の取り込み時の登録に委ねる。
夜の規則に従い検証済みの四本をコミットし、次の構造射の構成へ進む。

### 65.3 鎖のシフト遷移と有限単体による Γ の積

検証済みの追加三本は `EilenbergMacLaneShiftTransition`（72 行）、
`EilenbergMacLaneProbePair`（57 行）、`EilenbergMacLaneGammaPair`（56 行）。
smart 切断のシフトからの指定射・自然性・負次数の準同型性、
有限標準単体の AW 対角を用いた評価、実 Γ の二項積を供給した。
AW を大きい宇宙の Γ の台へ直接適用せず、小さい標準単体で評価している。

ビルドは `/tmp/bsw16/em-transition-04.log` と
`/tmp/bsw16/em-gamma-pair-05.log` で成功。監査
`/tmp/bsw16/audit-em-pairs.log` は十本・121 宣言・標準三公理のみ。
追加 185 行、(ii) の検証済み実測は計 504 行。新規警告・sorry・追加公理なし。
登録候補は上記三本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
スペクトル構造射・Ω 条件・置換の全自然性・native V はまだ未供給。
次は Γ の零元の照合を閉じて基点付き構造射へ接続する。

### 65.4 零基点・smash・基本円・指定構造射

以下の七本を検証した（全て `EInfinity/PowerOperation/`）。

| モジュール | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaZero | 67 |
| EilenbergMacLaneGammaPairNaturality | 48 |
| EilenbergMacLaneGammaAxes | 59 |
| EilenbergMacLaneGammaSmash | 72 |
| EilenbergMacLaneGammaSmashNaturality | 55 |
| EilenbergMacLaneCircle | 63 |
| EilenbergMacLaneSuspension | 46 |

追加計 **410 行**、(ii) の検証済み実測は **914 行**。
`gammaProbeEquiv_zero` と逆方向の照合、二項評価の両変数での自然性、
二つの零軸の零化から、既存 `ReducedPair` の普遍性で `gammaSmashPair` を作った。
基点付きの零射の大きな定義展開を避け、既存の一般補題を使っている。

基本円は固定した単位複体の第 1 段の π₁ で、指定 π/H 比較の逆像として定めた。
代表を選ぶのはこの固定対象だけで、複体変数ごとの選択はしない。
`unitCircle_class` と `unitCircle_homology` により、同じ類の計算を検証済み。
`gammaSuspension`・`levelSigma` は、この円・実 Γ の smash 積・左シフト同型を
合成した実際の構造射である。Ω 条件を新たな仮定として加えてはいない。
構造射の自然性の最終照合、Ω 条件、置換の全自然性と native V は未完。

最終ビルド `/tmp/bsw16/em-suspension-03.log` は成功（4,213 jobs）。
監査 `/tmp/bsw16/audit-em-suspension.log` は **17 本・201 宣言・標準三公理のみ**。
新規警告・sorry・追加公理なし。監査の終了と鍵の返却も回収済み。
登録候補は表の七本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
共通入口と共通監査は触らない。夜の規則に従い、報告後も自然性・Ω 条件の照合を続ける。

### 65.5 実 Kan 列の全関手と、零次数・全基点の比較

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneComponents | 53 |
| EilenbergMacLaneSuspensionNaturality | 53 |
| EilenbergMacLaneSequence | 64 |
| EilenbergMacLaneGammaWeakEquivalence | 62 |

追加 **232 行**、(ii) の検証済み実測は **1146 行**。
`levelPiZeroHomologyEquiv`・`levelPiZeroCohomologyEquiv` は各段の π₀ と H^r の比較。
`gammaSuspension_naturality`・`levelSigma_naturality` は任意の複体射について厳密な可換式。
これにより `eilenbergMacLaneSequenceFunctor` を実際の Kan 列の全関手として得た。
ここでは Ω 条件を入力した Ω スペクトルを実例と呼んでいない。

`gammaMap_kanPiIsomorphism_iff` は、同じ Γ の台の全基点・零次数を含む π 同型と、
指定 smart 切断射の準同型性の同値。既存の Moore 判定と実余単位の
`Arrow.isoMk` を使い、未供給の仮定や `[ModelCategory SSet]` を加えていない。

ビルド `/tmp/bsw16/em-sequence-03.log` で列の全関手が成功。
弱同値判定の修正後の最終ビルドは `/tmp/bsw16/em-gamma-weak-01.log` で成功。
監査 `/tmp/bsw16/audit-em-sequence.log` は **21 本・228 宣言・標準三公理のみ**。
最終の四本に警告・sorry・追加公理なし。終了を回収し、鍵を返却済み。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

残りは、指定 suspension 射の Ω 条件（π/H のシフトとの照合）、
逐次単射置換の全自然性、native Sp への全関手とその π/H の全自然比較。
対象ごとの群同型や列の通常の全関手だけから native V の完成とは扱わない。
この区切りの後も、夜の規則に従い (ii) の実装を続ける。

### 65.6 逐次単射置換の全関手性と準同型の保存

| 追加モジュール（`PowerOperation/`） | 行数 | 用途 |
| --- | ---: | --- |
| PointedFactorizationFunctor | 65 | ［一般∞］移動候補 |
| KanSequenceReplacementMaps | 91 | ［一般∞］移動候補 |
| KanSequenceReplacementFunctor | 99 | ［一般∞］移動候補 |
| EilenbergMacLaneQuasiIso | 47 | Γ の各段の準同型保存 |

追加 **302 行**、(ii) の検証済み実測は **1448 行**。
既存 `PointedFactorization.factorization` の実 SOA を変更せず、
正方形の中間対象への作用と左右因子の自然性を公開した。
既存の `KanSequence.replacementStage` と同じ段を帰納的に使い、
厳密な列の射への作用、恒等射・合成の保存、元の列への比較自然変換を証明。
`kanSequenceReplacementMap_piIsomorphism` は同じ比較自然変換の可換式から
段ごとの全基点 π 同型を移す。Ω 条件をまだ示していない対象を Sp と呼んでいない。

`smartTruncationMap_quasiIso` は零次数の境界を含む実 smart 切断の準同型保存。
`truncLEIso_inv_naturality` と `quasiIso_extendMap_iff` により、同じ切断射を運ぶ。
これを Γ の弱同値判定に接続し、元の準同型を各段の全基点 π 同型へ送った。

最終ビルド `/tmp/bsw16/em-replacement-quasi-01.log` は成功（4,764 jobs）、新規警告なし。
監査 `/tmp/bsw16/audit-em-replacement.log` は **25 本・268 宣言・標準三公理のみ**。
sorry・追加公理なし。終了・鍵返却を回収済み。登録候補は表の四本
（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
一般補助三本は EInfinity 下に置き、将来の場所は調整役に委ねる。
残りは指定 suspension 射の Ω 条件、その出力の native V と π/H の全自然比較。
夜の規則に従い、ここでも承認を待たずに (ii) を続ける。

### 65.7 Γ の加法・指定単位と、Ω 列からの native 図式

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaAdditivity | 71 |
| EilenbergMacLaneGammaBilinearity | 77 |
| EilenbergMacLaneGammaUnit | 67 |
| EilenbergMacLaneGammaUnitPoint | 48 |
| OmegaSequenceReplacementFunctor | 59 |
| OmegaSequenceNative | 41 |

追加 **363 行**、(ii) の検証済み実測は **1811 行**。
Γ の標準単体評価とその逆の加法性、指定 AW 積の両変数での加法性を示した。
`gammaUnitSimplex` は AW 余単位の実随伴像。`gammaUnitPoint` で全単体に整合させ、
`gammaPair_right_unit_point` は元の指定右単位子そのものを得る等式である。
この点は零基点とは区別される。

最後の二本は **［一般∞］移動候補**。Ω 列の充満部分圏に同じ逐次単射置換を制限し、
BF スペクトルへの通常の全関手を得た。`omegaSequenceNative` はその通常の nerve を
既存 `nerveToCoherent` で native Sp へ送る標準比較。頂点も同じ置換対象である。
これは一般の coherent 図式の厳密化や D(A) からの降下を済ませたという主張ではない。
Eilenberg–Mac Lane 列の Ω 条件そのものは引き続き未証明であり、V の実例は未供給。

最終ビルドは `/tmp/bsw16/em-gamma-bilinear-03.log`、
`/tmp/bsw16/em-native-unit-01.log`（native 比較の成功）、
`/tmp/bsw16/em-gamma-unitpoint-01.log`。
監査 `/tmp/bsw16/audit-em-unit.log` は **31 本・327 宣言・標準三公理のみ**。
最終六本に新規警告・sorry・追加公理なし。終了・鍵返却を回収済み。
登録候補は表の六本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
次は指定単位の零次数の係数と、基本円を使う Ω 比較の照合を続ける。

## 66. 夜の代わりの作業：M15 の一般 R 加群の段 0（紙のみ）

### 66.1 必要な一般性と型の案

`Shared/Descendable.lean` の一般形では、R は `(E.CAlg A)` の任意の頂点。
R を離散環 A の像に制限した D(A) の thick ideal で代用しない。
以下は **新しい名前の型案**であり、現存する宣言・検証済みコードではない。
`EInfinityTheory` に M15 の欄を加える提案でもない。

```lean
-- E : EInfinityTheory.{u}, A : Type u, [CommRing A]
-- R B : (E.CAlg A) _⦋0⦌, f : SSet.Edge R B
modulesOver (E : EInfinityTheory.{u}) (A : Type u) [CommRing A]
  (R : (E.CAlg A) _⦋0⦌) : SSet.{u+1}
modulesOverForget (R : (E.CAlg A) _⦋0⦌) :
  modulesOver E A R ⟶ derivedInfinityCategory A
moduleUnit (R : (E.CAlg A) _⦋0⦌) : (modulesOver E A R) _⦋0⦌
algebraAsModule (f : SSet.Edge R B) : (modulesOver E A R) _⦋0⦌
moduleTensorWith (R : (E.CAlg A) _⦋0⦌) (M : (modulesOver E A R) _⦋0⦌) :
  modulesOver E A R ⟶ modulesOver E A R
moduleRestrict (f : SSet.Edge R B) : modulesOver E A B ⟶ modulesOver E A R
moduleExtend (f : SSet.Edge R B) : modulesOver E A R ⟶ modulesOver E A B
```

単位加群から `algebraAsModule f` への指定辺が必要であり、台は `E.forget A` が送る f。
f の fiber は **modulesOver E A R の中で**取る。
指数 n の射は、その fiber の n 重相対テンソルから同じ単位加群への指定射。
`HasDescentIndexLEOver` はその射のホモトピー圏での零性、
`IsDescendableOver` は `algebraAsModule f` の生成する thick ⊗-ideal が同じ単位を含むこと。
両者を先に同値と定義してしまわず、同値は drafts の定理として証明する。

### 66.2 再利用できる宣言と、まだ比較が要る境界

- `DifferentialGraded.LeftModule`・`LeftModuleCategory`・`leftModuleEvaluationDG`・
  `leftModuleEvaluation` は dg 圏上の左加群の実構成。
  `DifferentialGraded.Module.Left.CategoryComparison` の `ringModuleEquivalence` は
  **定数一対象 dg 圏**での比較。一般の E∞ 頂点 R の加群圏の供給とは別。
- `CategoryTheory/Monoidal/Mod/BalancedTensor` の `BalancedTensor.obj`・`projection`・
  `desc`・`moduleBifunctor` は通常の内部加群と実 coequalizer の部品。
  元の環の単なる H⁰、または hD(A) の中の通常の代数対象へ移して終わりにはできない。
  derived relative tensor は適切な置換・bar の実現・native な比較を要する。
- 安定閉包には `StableInfinityCategories/StableVertexExtension`・
  `StableHoGeneration`・`CofiberLocalizingComposition` の既存の閉包の部品を再利用できる。
  これらだけでは相対テンソルでの閉性も、R 加群の台との比較も供給されない。
- 一般の R に関する restriction/extension は、辺の合成、指定された底変換四角形、
  単位・相対テンソルまでの比較が必要。対象ごとに R の厳密模型を選ぶだけでは
  `isDescendableOver_pushout`・`isDescendableOver_tensorMaps` の全自然な主張を閉じない。

BE の厳密代数の模型を使う場合でも、単なる通常の可換 dg 環と同一視してはならない。
BE 代数の可換性は高次の整合を含む。通常の `CommMon` の balanced tensor を
無条件にそのまま適用する経路は、必要な仮定が供給されていない。
BE の実例の内部で module の模型と比較を証明し、BS の利用側は模型の中身を参照しない形が必要。

### 66.3 証明の順序と、供給する比較

1. 一般 R の native な module 準圏、その単位と台の忘却を構成する。
   厳密模型を使う場合は、置換と同値な R に対する module 圏の同値まで含める。
2. 相対テンソル・restriction/extension の随伴、単位・結合性・対称性、
   f に沿う底変換の比較を作る。一般の coherent な R への降下を対象ごとの選択で省かない。
3. 安定性と tensor の有限余極限保存を示し、生成する thick ideal と
   fiber の指数射の零性の同値に進む。ここは E∞ を直接使わない一般補題へ分けられる。
4. 既存 drafts の AmitsurData の同じ増大錐を使って Tot 降下へ進む。
   ③-b の実現・Tot の橋との比較はこの段に置き、単なる次数ごとの同型で代用しない。
5. RHom・Frobenius colimit の指数評価・完備版を一般 R のまま供給する。
   drafts の `True := by trivial` は証明済みの項目とは数えない。

HA の地図の対応は §61.4 のまま：4.2.1.15、4.2.3.5・4.2.3.7、
4.5.1.1・4.5.2.1・4.5.3.1。descendability 自体は Mathew Definition 3.18・
Proposition 3.22、指数の利用は BS17 §11.2・Lemma 11.22。
この節は地図上の対応を一般 module 圏の既証明性と読み替えていない。

### 66.4 規模と後で要る分担判断

§61.4 の **一般 R 加群 2,500〜4,500 行**を、次の内訳で追跡する。

| 束 | 見込み（行） | 必須の出力 |
| --- | ---: | --- |
| 模型・native 比較 | 800〜1,500 | R と射に関する coherent な module 圏と台 |
| 相対テンソル・底変換 | 1,000〜1,800 | 単位・結合・対称・restriction/extension の比較 |
| 安定性・利用側への接続 | 700〜1,200 | fiber・thick ideal の一般性、指定単位と指定辺 |
| **計** | **2,500〜4,500** | |

これは実測ではなく見込み。一般の coherent な module 構成を他レーンが供給する場合は
適用の費用と二重計上しない。現存の通常の module API だけで最初の束を閉じられるとは
まだ確認していないので、M15 着手時に **一般の native module 圏と相対テンソルを誰が供給するか**
を決める必要がある（調整役の既存の予告どおり）。
RHom と完備版の正確な入力は A5 の利用側とすり合わせる。
新しい interface 欄、drafts の型変更、M15 の Lean 実装には着手していない。
この紙の作業にビルド・監査・新しい整理券は使っていない。M14 の (ii) は続行中。

## 67. D79(ii) 続行：指定基本円の照合と Γ の fiber 比較の前段

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneAdjointSuspension | 59 |
| EilenbergMacLaneSmashUnit | 70 |
| EilenbergMacLaneSuspensionUnit | 64 |
| EilenbergMacLaneUnitCoefficient | 36 |
| EilenbergMacLaneVertexUnit | 70 |
| PointedSmashUnitSeed | 31 |
| EilenbergMacLaneStandardHom | 46 |
| EilenbergMacLaneFibration | 59 |
| EilenbergMacLaneFiniteLimits | 57 |

追加 **492 行**。コメント警告の修正一行を含め、
(ii) の検証済み実測は **2304 行**。

### 67.1 指定射と零次数の照合

`gammaSmashPair_right_unit` は、基点付きの smash の積でも指定 AW 単位が
元の右単位子そのものを与える厳密な等式。
`gammaSuspension_on_unit` は、単位上の構造射の値を固定した `unitCircle` と
`unitShiftAutomorphism` の合成として元の圏で照合する。
二つの単位比較の差を、恒等射と仮定せず実際の自己同型として保持した。
`gammaAdjointSuspension` は随伴構造射の全複体上の自然変換。
単位の点の像も同じ随伴で厳密に照合した。

`gammaUnitSimplex_zero_coefficient` は実 DK 余単位と実切断包含の下で係数が一である計算。
`gammaVertexUnitHomEquiv` と `gammaUnit_vertex_generates` は **任意の Γ の頂点**を
指定単位の頂点からの複体射の像として厳密に回収する。
ここでも頂点ごとの新しい持ち上げの選択やホモトピー圏への弱化を使っていない。

### 67.2 Ω 条件への fiber 比較で再利用できた一般部分

`gammaStandardHomFunctorIso` は、元の正規化標準単体の Hom の全関手と
同じ Γ の全自然同型。`gammaMap_fibration` は既存の
`normalizedSimplex_reedyCofibrant` と `HomotopyFunctionComplex.cosimplicialHom_fibration`
から実射影 fibration を Γ の Kan fibration へ移す。
使うモデル構造は構成済みの `projectiveModelCategory A` だけで、
`[ModelCategory SSet]` の仮定は加えていない。

`extendSmartTruncationAdjunction` は既存の実 Hom 同値を自然性ごと随伴へ束ねたもの。
`gammaFunctor_preservesFiniteLimits` は smart 切断・実 Γ・加群の台の各因子から有限極限保存を示す。
これにより cone の strict fiber を同じ Γ の strict fiber へ移す経路を使える。
実際の指定随伴構造射がその loop 比較で π 同型になる証明は、まだ完了していない。

### 67.3 検証と登録候補

最終対象ビルドは `/tmp/bsw16/em-smash-unit-02.log`、
`em-suspension-unit-03.log`、`em-unit-coefficient-01.log`、`em-vertex-unit-02.log`、
`em-fibration-limits-02.log`（fibration と随伴の成功）、`em-finite-limits-05.log`。
監査 `/tmp/bsw16/audit-em-cone-prelim.log` は **40 本・397 宣言・標準三公理のみ**。
本体に sorry・追加公理なし。
`EilenbergMacLaneSuspensionNaturality` の heartbeat の理由をコメントに追加し、
その linter 警告も解消した。既存の公開宣言の型・証明の変更はない。

登録候補は表の九本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`PointedSmashUnitSeed` は **［一般∞］移動候補**として EInfinity 下に置いた。
共通入口・共通監査は変更していない。監査終了と鍵返却を回収済み。
この区切りでも止まらず、Γ の cone の比較から Ω 条件へ進む。


## 68. D79(ii)：cone の strict fiber と loop 側の保存性

追加五本は `EilenbergMacLaneConeFibration`（62 行）、
`EilenbergMacLaneConePullback`（57 行）、`EilenbergMacLanePointedLimits`（46 行）、
`EilenbergMacLaneLoopProperties`（64 行）、`ShortExactPullbackZero`（35 行）。
計 **264 行**、(ii) の検証済み累計 **2568 行**。
登録候補はこの五本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ShortExactPullbackZero` は **［一般∞］移動候補**。

`coneProjection_projectiveFibration` は実際の cone の第三射について既存の次数付き
section を使う。`gammaCone_isPullback` は回転 cone の短完全列を、同じ四射の
Γ の引き戻しへ移す。`gammaIdentityCone_zero_piIsomorphism` は恒等射の cone から
零複体への指定零射の全基点 π 同型。Γ と loop Γ の有限極限・零射の保存、
loop Γ の実射影 fibration と準同型の保存も証明した。
指定構造射の Ω 条件と native な V の降下は引き続き未完了。

対象ビルド `em-cone-pullback-02.log`、`em-cone-pullback-04.log`、
`em-loop-properties-02.log` は成功（最終版で警告なし）。
監査 `/tmp/bsw16/audit-em-cone-properties.log` は **45 本・420 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則に従い、報告後も持ち上げ性と接続写像の比較へ続行する。


## 69. D79(ii)：指定構造射の Ω 条件の次数移動

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| ConeFiberHomotopyComparison | 58 |
| ContractibleTotalConnecting | 46 |
| EilenbergMacLaneConeContractibility | 48 |
| EilenbergMacLaneLoopTrivialFibration | 48 |
| EilenbergMacLaneOmegaDimensionShift | 50 |
| EilenbergMacLanePointedConeFiber | 57 |
| EilenbergMacLaneTrivialFibration | 70 |
| PointedConnectingComparison | 42 |
| PointedContractibleConnecting | 81 |
| PointedHomotopyIso | 34 |
| TerminalKanHomotopy | 48 |

追加 **582 行**、(ii) の検証済み累計 **3150 行**。
表の十一本が登録候補（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ContractibleTotalConnecting`、`PointedConnectingComparison`、
`PointedContractibleConnecting`、`PointedHomotopyIso`、`TerminalKanHomotopy` は
**［一般∞］移動候補**。

### 69.1 実際に閉じた主張

`gammaMap_monomorphisms_rlp` は実射影 trivial fibration を同じ Γ の
全単射 RLP へ移す。正規化標準単体の Reedy cofibration を使い、SSet の
モデル構造は仮定しない。loop Γ にも同じ持ち上げ性を移した。
恒等 cone の Γ・loop Γ の全基点・全次数のホモトピー類は一元であり、
終対象射に全境界の充填がある。

`pointedConeFiberIso` は元の回転 cone の kernel と指定点付き fiber の厳密な同型。
その二つの脚と自然変換に対する自然性も元の圏で照合した。
零次数を含む接続同値と自然性を既存の接続写像そのもので束ね、
`gammaAdjointSuspension_bijective_iff_shift` を証明した：指定構造射の M における
π_n の全単射性と、M[1] における π_{n+1} の全単射性が同値になる。

これは **Ω 条件の完成ではない**。全複体での零次数の比較と任意の基点への移送、
その後の native な V の降下・自然な π/H 比較が残る。
(i) の界面の型は変更していない。

### 69.2 検証

対象ビルド `em-pointed-cone-fiber-02.log`、`em-cone-contractible-02.log`、
`em-loop-trivial-fibration-01.log`、`em-pointed-connecting-03.log`、
`em-omega-dimension-shift-01.log` は成功（最終版に警告なし）。
監査 `/tmp/bsw16/audit-em-omega-dimension.log` は **56 本・463 宣言・標準三公理のみ**。
sorry・追加公理なし。鍵返却を回収済み。共有入口・共有監査は未変更。
夜の規則どおり止まらず、零次数への帰着と指定基本円の比較を続ける。


## 70. D79(ii)：標準基点の全次数を零次数へ帰着

`PointedNaturalIsoDetection`（40 行、**［一般∞］移動候補**）と
`EilenbergMacLaneOmegaZeroReduction`（39 行）を追加。
(ii) の検証済み累計 **3229 行**。登録候補はこの二本
（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

`gammaAdjointSuspension_bijective_of_zero` は、全複体での零次数の全単射性を入力に取り、
同じ指定構造射の標準基点での全次数の全単射性を与える。
前節の恒等 cone の次数移動と実際の M[-1][1] ≅ M の同型を用いる。
零次数の全単射性を公理として追加したものではなく、未完了の主張を明示した帰着。
任意の基点での Ω 条件、native な V、安定 π/H 比較はまだ未完了。

対象ビルド `/tmp/bsw16/em-omega-zero-reduction-01.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-omega-zero.log` は **58 本・465 宣言・標準三公理のみ**。
sorry・追加公理なし。鍵返却を回収済み。引き続き零次数の指定 π/H 比較を進める。


## 71. D79(ii)：元の Γ の自然な π/H 比較と指定頂点

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneGammaCohomotopy | 82 |
| EilenbergMacLaneGammaComponents | 79 |
| EilenbergMacLaneNaturalVertex | 63 |
| EilenbergMacLaneTruncationNaturality | 54 |

追加 **278 行**、(ii) の検証済み累計 **3507 行**。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。

`smartTruncationHomologyIso_naturality` は指定延長同型と smart 切断包含の自然性。
`gammaPiZeroCohomologyEquiv` と `gammaPiCohomologyEquiv` はシフト零を挟まず、
元の Γ の零・正次数を同じ正規化余単位で元の H へ戻し、全複体射で自然になる。
`gammaAdjointSuspension_vertex_value` は、指定構造射の任意の頂点での値を、
指定単位の頂点からの複体射の像として **元の圏で厳密に**回収する。
同じ原理で、単位の頂点の値が等しい二つの自然変換の連結成分の写像が一致する。

これで Ω 条件の零次数の計算に使う自然性が揃った。
零次数で実際に全単射になるという主張、全基点への移送、native な V の降下、
安定 π/H の自然同型は未完了。型や範囲の変更の判断は新たに発生していない。

対象ビルド `/tmp/bsw16/em-gamma-cohomotopy-03.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-gamma-comparison.log` は **62 本・504 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、実 π₀/Moore 比較の代表元の計算へ続行する。


## 72. D79(ii)：零単体の実ホモロジー類の計算

追加三本は `MooreZeroRepresentative`、`ChainZeroClassNaturality`、
`EilenbergMacLaneGammaZeroRepresentative`（接頭辞
`SerrePositivity.EInfinity.PowerOperation.`、いずれも登録候補）。
計 **132 行**、(ii) の検証済み累計 **3639 行**。
前二本は **［一般∞］移動候補**。

`modulePiZeroMooreEquiv_mk` は、元の π₀/Moore 比較が代表頂点を
同じ実 opcycles 射で写すことの等式。
`mooreDegreeZeroIso_eq` は二つの既存の零次数同型が同じ正規化包含からなることの照合。
`gammaPiZeroTruncationEquiv_mk` はこれを指定 Dold–Kan 余単位で写し、
元の Γ の頂点の像を指定 smart 切断の零次ホモロジー類として計算する。
元の複体へ戻す比較と単位の類の計算は続行中。

対象ビルド `/tmp/bsw16/em-gamma-zero-representative-03.log` は成功、警告なし。
監査 `/tmp/bsw16/audit-em-gamma-representative.log` は **65 本・513 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり次の代表元の比較へ進む。


## 73. D79(ii)：指定単位・loop の頂点と零次の自然写像

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| CochainZeroCycleClass | 43 |
| EilenbergMacLaneGammaUnitClass | 72 |
| EilenbergMacLaneLoopComponents | 62 |
| EilenbergMacLaneSmartZeroCycle | 61 |
| EilenbergMacLaneUnitLoopVertex | 67 |
| EilenbergMacLaneVertexClass | 37 |
| UnitPrecompositionHomology | 77 |
| EilenbergMacLaneZeroCohomologyMap | 76 |

追加 **495 行**、(ii) の検証済み累計 **4134 行**。
登録候補は表の八本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`CochainZeroCycleClass` は **［一般∞］移動候補**。

`gammaPiZeroCohomologyEquiv_unit` は同じ π₀/H⁰ 比較が指定 AW 単位を
元の単位類へ写す等式。`gammaPiZeroCohomologyEquiv_mk` は任意の Γ の頂点の像を、
実随伴で回収した指定複体射の元の H⁰ の類として計算する。
`gammaAdjointSuspension_unit_vertex` は単位での構造射の頂点を固定した基本円と
指定自己同型による loop の頂点と **元の圏で厳密に**照合する。
既存の零 loop 比較の下では、その円の基本群の類の逆元になることも照合した。
逆元の向きを消したり、基本円を選び直したりしていない。

`gammaLoopPiZeroCohomologyEquiv` は loop Γ(M[1]) の成分を元の H⁰(M) と比較し、
全複体射に自然。`gammaSuspensionH0Map` は元の構造射を二つの比較で共役した
H⁰ 上の自然写像で、その全単射性と元の零次構造射の全単射性を同値にした。
`homologyZeroNatural_bijective_of_unit_iso` は、この自然写像の単位での値が
実単位自己同型の類なら全複体で全単射になるという検出補題。
**実際の単位自己同型の同定は続行中**で、Ω 条件や V の完成はまだ主張しない。

対象ビルド `em-smart-zero-cycle-03.log`、`em-gamma-unit-class-02.log`、
`em-unit-loop-vertex-01.log`（VertexClass と LoopComponents の成功）、
`em-unit-homology-detection-01.log`（UnitLoopVertex の最終改行版の成功）、
`em-zero-homology-map-01.log`（ZeroCohomologyMap の成功）、
`em-unit-homology-detection-02.log`（UnitPrecompositionHomology の成功）。
最終版の対象に警告なし。監査 `/tmp/bsw16/audit-em-zero-unit.log` は
**73 本・593 宣言・標準三公理のみ**。sorry・追加公理なし。
共有入口・共有監査は未変更、鍵返却を回収済み。夜の規則どおり続行。


## 74. D79(ii)：指定構造射の標準基点での全次数の全単射性

追加三本は `EilenbergMacLaneUnitDeshift`、`EilenbergMacLaneUnitVertexClass`、
`EilenbergMacLaneUnitH0Value`（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`、登録候補）。
計 **221 行**、(ii) の検証済み累計 **4355 行**。

`unitDeshiftAutomorphism` はシフト関手の充満忠実性で同じ指定自己同型を
実単位の自己同型へ戻す。`signedUnitDeshiftAutomorphism` は零 loop 比較の逆元を
その実際の自己同型の負号として保持する。
`gammaSuspensionH0Map_unit` は指定 H⁰ 写像の単位での値を、この自己同型の類と厳密に同定する。
したがって `gammaAdjointSuspension_bijective_at_basepoint` が閉じた：
**同じ指定随伴構造射は、全複体・全自然数次数で標準の零基点のホモトピー類に全単射**。
単位での等式を仮定に残していない。

残りは任意の基点の Ω 条件、native な V の降下、安定 π/H の自然同型。
任意の基点への移送は、可縮な全空間を持つ cone の固定 fiber を、その各頂点を
参照点とする接続同値で比較する。底の他の連結成分の同型を仮定する循環は避ける。

対象ビルド `em-unit-deshift-02.log`、`em-unit-h0-value-01.log`（UnitVertexClass の成功）、
`em-unit-h0-value-02.log` は成功、最終版で警告なし。
監査 `/tmp/bsw16/audit-em-based-omega.log` は **76 本・627 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、全基点の比較を続行する。


## 75. D79(ii)：全基点の Ω 列、実スペクトル関手、整数 π/H

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| ContractibleFiberComparison | 84 |
| EilenbergMacLaneOmegaAllBasepoints | 78 |
| EilenbergMacLaneOmegaSequence | 52 |
| EilenbergMacLaneSpectrumFunctor | 43 |
| EilenbergMacLaneSpectrumCohomology | 51 |

追加 **308 行**、(ii) の検証済み累計 **4663 行**。
登録候補は表の五本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ContractibleFiberComparison` は **［一般∞］移動候補**。

`gammaAdjointSuspension_kanPiIsomorphism` が閉じた：**同じ指定随伴構造射は
全複体・全基点・零次数を含む全次数で π 同型**。
可縮な全空間を持つ固定 fiber を、その各頂点の接続同値で比較した。
底の他の連結成分の同型を入力する循環や、加法による translation の新構成は不要だった。

`eilenbergMacLaneSequence_omega` は添字の加法の同じ同型も含めて元の Kan 列を Ω 列にする。
`eilenbergMacLaneSpectrumFunctor` は全複体と厳密な鎖写像から、既存の逐次単射置換による
実 `OmegaSpectrum` への関手。準同型の像は全段で π 同型になる。
`eilenbergMacLaneSpectrumPiCohomologyEquiv` は実スペクトルの整数 π_j と元の H^{-j} の群同型。
標準計算段の同じ置換射を使い、安定 π を独自の代用品に置き換えていない。
スペクトルの模型は §65 のまま `KST.Spectra.Sp`、対称スペクトルとの同一視は仮定しない。

**未完了**：この整数比較の全鎖写像での自然性、通常の複体圏の nerve から
既存 D(A) の dg nerve への coherent な降下、その上での native π/H の関手同型。
`eilenbergMacLaneOrdinaryNative` は通常の nerve 上の図式であり、V_A 完成とは呼ばない。
界面や drafts の型の追加変更はない。

対象ビルド `em-contractible-fiber-comparison-02.log`、`em-omega-all-basepoints-01.log`、
`em-spectrum-functor-01.log`（SpectrumFunctor の成功）、`em-spectrum-cohomology-01.log`
（OmegaSequence の改行警告修正を含む）は成功。最終版に警告なし。
監査 `/tmp/bsw16/audit-em-spectrum.log` は **81 本・650 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、自然性と native な降下へ続行する。


## 76. D79(ii)：native な hammock 因子化と既存 D(A) への比較

| 追加モジュール（`PowerOperation/`） | 行数 |
| --- | ---: |
| EilenbergMacLaneNativeWeak | 49 |
| ComplexHammockSource | 98 |
| EilenbergMacLaneHammockFunctor | 60 |
| ComplexHammockEssentialSurjectivity | 70 |

追加 **277 行**、(ii) の検証済み累計 **4940 行**。
登録候補は表の四本（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）。
`ComplexHammockSource`、`ComplexHammockEssentialSurjectivity` は **［一般∞］移動候補**。

### 76.1 native な側で閉じた主張

通常の複体図式から Sp への実写像は、元の準同型の辺を可逆辺へ送る。
既存の `modelHammock_isLocalization` と構成済みの実射影モデル・右 frame の族を用い、
全複体の同じ相対圏の hammock から native Sp への実関手
`eilenbergMacLaneHammockFunctor` を構成した。
元の複体図式へ戻る指定同型は点ごとの存在ではなく **全関手の `FunctorIso`**。
満たせないモデル構造の仮定や、関手の存在の追加公理はない。

同じ hammock から既存 `derivedInfinityCategory A` への実比較
`complexHammockDerivedComparison` と、その指定全関手同型も構成した。
元の半自由閉零圏上の比較を頂点へ評価し、
`complexHammockDerivedComparison_essentiallySurjective` まで閉じた。
Hom の宇宙の異なる通常 nerve の写像は元の同じ合成可能射列で作った。
既存 D(A) を別模型へ定義変更していない。

### 76.2 次の橋と現在の不足

残る主張の型は、既存界面の型を変えるものではない：

```lean
-- 未証明の次の比較。まだ本体の宣言としては置いていない。
lemma complexHammockDerivedComparison_fullyFaithful
    (A : Type u) [CommRing A] :
    IsFullyFaithful (complexHammockDerivedComparison A)
```

`normalizedOrdinaryDerivedHomMap_homotopyEquivalence` と
`normalizedTensorElementOrdinaryPinchedMap_weak`（K-projective 入力）は本体にある。
右 frame と hammock の全族比較も `FrameHom/` にある。
これらを二つの写像空間の同値の存在として並べるだけでは不十分で、
**指定比較関手とその sourceIso の下で、元の要素屋根族を運んだ射が一致すること**を
照合する必要がある。その後に本質的全射性と合わせて同じ比較を同値にし、
逆を通して既存 D(A) から Sp への V を作る。
この充満忠実性は現時点で未完了。V の完成や D79(ii) の終了は宣言しない。
整数 π/H の全鎖写像に対する自然性も続行中。

### 76.3 検証

対象ビルド `em-hammock-source-01.log`（NativeWeak の警告修正を含む成功）、
`em-hammock-functor-01.log`（ComplexHammockSource の最終版の成功）、
`em-hammock-essential-01.log`（HammockFunctor の改行版の成功）、
`em-hammock-essential-04.log` は成功。最終版に警告なし。
監査 `/tmp/bsw16/audit-em-native-hammock.log` は **85 本・695 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更、鍵返却を回収済み。
夜の規則どおり、報告後も自然性と指定屋根族の比較へ進む。

## 77. D79(ii)：同じ置換射を通る段ごとの π/H 自然性

登録候補（接頭辞 `SerrePositivity.EInfinity.PowerOperation.`）：
`EilenbergMacLaneStageCohomologyNaturality`（66 行）、
`EilenbergMacLaneSpectrumLevelNaturality`（78 行）。追加 **144 行**、
(ii) の検証済み累計 **5084 行**。

シフトのホモロジー比較と添字の移送の自然性を、元の Γ の段の自然性へ合成した。
次に `eilenbergMacLaneSpectrumMap_projection` で、同じ実単射置換射の
厳密な可換式を証明し、任意の正次数の計算段の π/H 自然性
`eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt_naturality` を閉じた。
ここでも元の鎖写像の厳密な可換式を保持している。

対象ビルド `em-stage-cohomology-naturality-02.log`、
`em-spectrum-level-naturality-04.log` は成功、最終版に警告なし。
監査 `audit-em-stage-naturality.log` は **87 本・709 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
整数次数の自然性と、§76.2 の指定比較の充満忠実性は続行する。

## 78. D79(ii)：整数 π/H の自然同型と指定正規化屋根の弱同値性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| EilenbergMacLaneSpectrumPiNaturality | 85 |
| EilenbergMacLaneSpectrumHomologyIso | 38 |
| ComplexNormalizedCommonFrame | 69 |
| ComplexNormalizedRoofMaps | 58 |
| ComplexNormalizedRoofWeak | 95 |

追加 **345 行**、(ii) の検証済み累計 **5429 行**。
後ろ三本は **［一般∞］移動候補**（複体模型に関する比較）。

### 78.1 整数 π/H の全鎖写像に対する比較

`eilenbergMacLaneSpectrumPiCohomologyEquiv_naturality` を閉じた。
標準計算段への次数移送の既存自然性と、§77 の同じ置換射の自然性を合成した。
`eilenbergMacLaneSpectrumPiCohomologyEquiv_apply` は、元の指定比較の順写像と
計算段の比較の厳密な等式である。局所的な略記を展開して接続することで、
不要な模型の定義展開による elaboration の時間切れを解消した。

`eilenbergMacLaneSpectrumHomologyIso A j` は、全複体の通常の圏上の
**関手全体の自然同型**
`eilenbergMacLaneSpectrumFunctor A ⋙ OmegaSpectrum.homotopyFunctor j ≅
complexMultiplicativeCohomology A j` である。
既存 D(A) 上の自然同型とはまだ区別する。

### 78.2 指定屋根の弱同値性

元の標準 frame と正規化テンソル frame の同じ共通置換を使い、左右の実射、
augmentation の厳密な三角形を明示した。
全要素圏の実比較の反転性を通して、
`complexNormalizedTensorRoof_weak` を閉じた。
これは写像空間の抽象的な同値の存在でなく、同じ全単体の屋根写像そのものの弱同値性。
`[ModelCategory SSet]` の未供給の仮定はない。

次は同じ全要素屋根を相対圏へ送り、`RoofPrefix.native_family_postcomp_column_roof_arrow`
と `NerveColumn.roof_naturality` に指定 sourceIso を代入する。
これで §76.2 の残りの指定比較の実写像空間への作用を照合する。
D(A) から Sp への V と (ii) の終了はまだ宣言しない。

### 78.3 検証

`em-spectrum-pi-naturality-08.log`、`em-pi-and-roof-03.log` の
`ComplexNormalizedRoofWeak`、`em-homology-iso-01.log` は成功。
最終版の五本に警告なし。
監査 `audit-em-pi-roof.log` は **92 本・743 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 79. D79(ii)：同じ native な屋根族と指定比較の全パラメータ照合

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| ComplexRelativeElementColumn | 53 |
| ComplexRelativeElementPinchedFamily | 63 |
| ComplexRelativeElementSourceRoof | 62 |
| FullyFaithfulWeakRoofDetection | 32 |
| ComplexRelativeElementIndexComparison | 75 |
| ComplexRelativeElementRoofMaps | 107 |
| ComplexRelativeColumnHom | 62 |
| ComplexRelativeElementWeak | 58 |

追加 **512 行**、(ii) の検証済み累計 **5941 行**。
全八本が **［一般∞］移動候補**（うち七本は複体模型の比較）。

### 79.1 今回閉じた接続

全要素圏を同じ全複体の相対圏へ送り、
`complexRelativeElementHammockPinchedMap` を構成した。
`complexRelativeElementPinchedFamily_comparison_arrow` は、
**指定した** `complexHammockDerivedComparison` による同じ全族の像が、
同じ augmentation の逆と評価であることの全 Arrow の等式。
`complexRelativeElementSourceRoof_naturality` は、
**指定した sourceIso** と同じ全屋根との全関手の可換式である。

宇宙の表示変更は `complexRelativeElementIndexIso` の実同型。
`complexRelativeElementRoof_graph_image`・`complexRelativeElementRoofMap_image`
は全語の標準射・二脚・全縦射を保つ厳密な等式。
これらで §78 の同じ屋根の弱同値性を運び、
`complexRelativeElementHammockPinchedMap_weak` を閉じた。
`complexRelativeColumnHom_arrow` は元の通常複体円柱への全制限を回収する。

充満忠実性の検出は `fullyFaithful_of_weak_roof` に分離した。
必要な入力は、同じ族 p と **p ≫ pinchedHomMap F** の両方の弱同値性であり、
抽象的な写像空間の同値の存在を代用していない。
次は通常導来屋根への回収を同じ全族へつなぎ、指定比較の誘導射を検出する。
§76.2 の充満忠実性、既存 D(A) 上の V はまだ未完了。

### 79.2 検証

`em-relative-source-roof-01.log`、`em-relative-roof-maps-03.log` の
IndexComparison、`em-relative-roof-maps-04.log` の RoofMaps、
`em-relative-weak-02.log` の ColumnHom、`em-relative-weak-03.log` は成功。
最終版に警告なし。
監査 `audit-em-relative-roof.log` は **100 本・784 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 80. D79(ii)：指定 hammock 比較の全写像空間の橋を完了

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| ComplexRelativeElementDerivedRoofComparison | 59 |
| NerveColumnConstantRestriction | 47 |
| NerveColumnRoofConjugation | 67 |
| ComplexRelativeElementTransport | 66 |
| ComplexRelativeElementReference | 78 |
| ComplexHammockPinchedComparison | 62 |
| ComplexHammockProbeFunctor | 60 |
| FullyFaithfulEquivalencePrecomposition | 30 |
| ComplexHammockProbeVertices | 51 |
| ComplexHammockFullyFaithful | 48 |

追加 **568 行**、(ii) の検証済み累計 **6509 行**。
全十本が **［一般∞］移動候補**（うち七本は複体模型に関する比較）。

### 80.1 §76.2 の不足を閉じた

`complexHammockDerivedComparison_fullyFaithful` を **全頂点・全写像空間**で証明した。
同じ指定 sourceIso の全屋根の自然性を、同じ頂点成分による両端の輸送へつなぎ、
`complexRelativeElementDerivedPinchedMap_reference_family` で元の通常導来屋根と
全パラメータの関手の射として照合した。その元の弱な基準族で反映し、
`complexHammockDerivedComparison_probe_pinched_weak` により
**指定比較そのものの実 pinched 誘導射**を検出した。

元の `framedLimitProbeFunctor` と同じ augmentation が hammock 上で自己同値を
誘導することも証明した。その自己同値の全頂点での値を厳密に照合し、
probe の像での検出を全頂点へ延ばした。
比較を別の関手へ取り替えたり、ホモトピー圏上の充満忠実性で代用したりしていない。

したがって、以前の本質的全射性と合わせて、同じ全複体 hammock 比較を
既存 D(A) との実同値にできる。次はその逆を通して native な V を作り、
既存 D(A) 上の π/H 自然同型へ降ろす。
(ii) の終了はその比較まで検証してから報告する。

### 80.2 検証

`em-relative-derived-roof-02.log`、`em-constant-restriction-01.log`、
`em-relative-transport-reference-02.log` の RoofConjugation、
`em-relative-transport-reference-03.log` の Transport、`em-relative-reference-04.log`、
`em-pinched-probe-01.log` の PinchedComparison、`em-hammock-probe-02.log`、
`em-hammock-fully-faithful-02.log` は成功。最終版の十本に警告なし。
監査 `audit-em-fully-faithful.log` は **110 本・821 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。

## 81. D79(ii)：既存 D(A) から native Sp への実 V と全 sourceIso

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| EilenbergMacLaneDerivedFunctor | 58 |
| ComplexRelativeNerveUp | 35 |
| EilenbergMacLaneDerivedSourceComparison | 47 |
| OrdinaryNerveHomotopyFunctor | 32 |
| OmegaSpectrumHoFunctor | 32 |
| EilenbergMacLaneNativeHomologyIso | 28 |

追加 **232 行**、(ii) の検証済み累計 **6741 行**。
ComplexRelativeNerveUp・OrdinaryNerveHomotopyFunctor・OmegaSpectrumHoFunctor は
**［一般∞］移動候補**。実 V は基礎の k に関する構成なので、将来の基盤移管の対象。

### 81.1 実 V を構成した

同じ比較を本質的全射性と合わせて `complexHammockDerivedEquivalence` にし、
その逆を通して `eilenbergMacLaneDerived : derivedInfinityCategory A ⟶ KST.Spectra.Sp`
を構成した。特に要求された V_{F_p} をこの実関手の実例として取れる。
既存 D(A) や native Sp の定義の変更、関手の存在の追加入力はない。

`eilenbergMacLaneDerived_sourceIso`・`ordinarySourceIso`・`semifreeSourceIso` は、
元の相対全複体・通常全複体・半自由閉零圏での **全関手の指定同型**。
対象ごとの同型の存在だけを結論にしていない。

`eilenbergMacLaneNativeHomologyIso` は、元の全複体の通常関手上で、
native Sp の実際の `SpectrumHo.piFunctor` と H^{-j} との全自然同型。
残るのは、半自由閉零圏上の全 sourceIso を通し、
**既存 D(A) のホモトピー圏上**で界面が要求する π/H 自然同型へ降ろす部分。
したがって (ii) 全体の終了、P⁰ の存在や計算の完了はまだ宣言しない。

### 81.2 検証

`em-derived-functor-02.log`、`em-derived-source-comparison-01.log` の SourceComparison、
`em-ordinary-nerve-ho-02.log`、`em-native-homology-01.log` の
OmegaSpectrumHoFunctor・NativeHomologyIso は成功。最終版の六本に警告なし。
監査 `audit-em-derived-functor.log` は **116 本・849 宣言・標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
全見込み 14,500 行の半分の 7,250 行にはまだ届いていない。夜の規則どおり続行する。


## 82. D79(ii) 完了：既存 D(A) の全ホモトピー圏上の π/H 自然同型

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| DGClosedHoComparison | 56 |
| DGClosedHoFull | 43 |
| NatIsoFullEssentialDescent | 37 |
| OrdinaryNerveHoNaturality | 41 |
| OmegaSpectrumNativeHoComparison | 49 |
| EilenbergMacLaneNativeDiagram | 65 |
| SemifreeClosedHoHomology | 56 |
| EilenbergMacLaneSemifreePiComparison | 58 |
| EilenbergMacLaneDerivedHomologyIso | 48 |

追加 **453 行**、(ii) の検証済み累計 **7194 行**。
DGClosedHoComparison・DGClosedHoFull・NatIsoFullEssentialDescent・
OrdinaryNerveHoNaturality・OmegaSpectrumNativeHoComparison・SemifreeClosedHoHomology は
**［一般∞］移動候補**。他の三本も V の基盤移管時の比較の対象。

### 82.1 完成した比較と範囲

`eilenbergMacLaneDerived_homologyIso A i` は、界面と同じ型

```lean
hoMap (eilenbergMacLaneDerived A) ⋙ SpectrumHo.piFunctor (-i) ⋙
  CommGrpCat.toAddCommGrp ≅ additiveCohomologyOnHo A i
```

の **全関手の自然同型**。半自由閉零圏から native D(A) のホモトピー圏への
充満・本質的全射性を証明し、同じ semifreeSourceIso 上の比較を降ろした。
通常の複体のホモロジーだけで結論を代用していない。
§81 の実 V と合わせ、要求された **V_{F_p} と π/H 比較までを完了**した。
一般 A でも同じ構成が使えるが、係数制限に関する全比較は今回の完成範囲に含めない。
P⁰ とその次数計算、離散・Tot の照合は未完了。次は (iii) の Tate 経路を進める。

### 82.2 検証

`em-derived-homology-03.log`：最終対象ビルド成功（12,561 jobs）。
追加九本の最終版に警告なし。依存の Interface/Theory に以前からある長行警告は残る。
`audit-em-derived-homology.log`：**125 本・894 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口と共有監査は未変更。
見込み上端の半分 7,250 行まであと 56 行。到達時に実測と残見込みを報告し、
夜の規則どおり停止せず (iii) を続行する。


