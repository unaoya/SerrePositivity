# 概念の定義書：B 複体と dg 圏

小概念は out/remap-*.csv（B・D・F の担当分）の new_subconcept と一致する。ほかの大分類の担当が同じ概念へ送る小概念はここには入っていない。

## B 複体と dg 圏/dg 代数のホモトピー論

**入るもの**：dg 代数の一般のホモトピー論：胞体分解（セルの付加）、path 対象、ホモトピー引き戻しの模型、写像空間（「H/局所化不変量：Postnikov と平方零拡大」から出す分）。

**入らないもの**：
- dg 代数を一対象 dg 圏と見ること、dg 代数の射が定める dg 関手は「B/dg 圏と dg 関手」へ。
- Postnikov 切断と平方零拡大に固有のものは「H/局所化不変量：Postnikov と平方零拡大」へ。
- dg 代数の Milnor 四角形（貼り合わせとの比較）は「D/dg の貼り合わせ」へ。
- オペラド代数（E 代数）のモデル構造とセル代数は「F/dg オペラドと代数」「F/E∞ 代数の圏（CAlg と加群）」へ。
- dg 圏の cell 分解は「B/dg 商と cell 分解」へ。

## B 複体と dg 圏/dg 加群

**入るもの**：dg 圏上の右・左 dg 加群の厳密な水準：対象、Hom 複体（豊穣 end）、閉次数零の加群圏、表現可能加群、写像錐、ホモトピー圏 K(D)、擬同型と acyclic 加群、ホモトピー射影的・半自由な加群と分解、dg 前三角性。

**入らないもの**：
- 擬同型で局所化した導来圏 D(D)、Perf、有限 cell 対象、Perf の dg 増強は「B/導来圏と Perf（dg 加群）」へ。
- 加群の dg 神経（導来 ∞ 圏の模型）は「D/導来 ∞ 圏」へ。
- 双加群、balanced テンソル積、K-flat 性は「B/双加群とテンソル」へ。
- 加群の係数拡大・係数制限は「B/係数の取り替え」へ。
- 環上の普通の加群は「A/環と加群（その他）」へ。E 代数上の加群は「F/E∞ 代数の圏（CAlg と加群）」へ。
- 図式から作る coherent bar 加群は「D/coherent bar 構成」へ。

**小概念**：
- Hom 複体（豊穣 end）
- ホモトピー圏 K(D)・擬同型・acyclic 加群
- ホモトピー射影的加群
- 写像錐
- 右 dg 加群と左 dg 加群
- 表現可能加群と双対
- 閉次数零の加群圏 Z⁰ と評価関手
- dg 前三角性（表現可能加群の同型閉包が零・シフト・cone で閉じる）

**文献**：
- Keller §1.2
- Keller §2.2, §4.1
- Keller §3.1; Spaltenstein
- Keller §2
- Keller, Deriving DG categories §1
- Keller §1.2（米田）
- Bondal–Kapranov

## B 複体と dg 圏/dg 商と cell 分解

**入るもの**：Drinfeld の dg 商（path 複体、ε を足した Hom 複体、普遍性、path 長のフィルター）と、dg 圏への cell の貼り付け・cell 分解（Hom が K-flat な分解）、dg 商と Verdier 商の比較。

**入らないもの**：
- dg 商の上の係数変更の関手は「B/係数の取り替え」へ。
- cell 分解した dg 圏の dg 商の神経と thick 閉包の核（resolvedDGQuotientNerve など）は「D/Verdier 列」へ。
- 三角圏としての Perf の Verdier 商は「B/導来圏と Perf（dg 加群）」へ。
- 自由 dg 圏（quiver から）は「B/dg 圏と dg 関手」へ。局所 K-flat な dg 圏による分解 KFlatDGResolution は「B/双加群とテンソル」の「K-flat 性と K-flat 分解」のまま（境目が近い）。
- dg 代数の胞体分解は「B/dg 代数のホモトピー論」へ。

**小概念**：
- cell の貼り付け
- cell 分解（Hom が K-flat な分解）
- dg 商と Verdier 商の比較
- dg 商の path 複体
- dg 商の普遍性（収縮つき dg 関手）
- dg 商圏（Hom 複体・包含関手・収縮元 ε）
- path 長のフィルトレーション

**文献**：小概念の reference に記載なし。

## B 複体と dg 圏/dg 圏と dg 関手

**入るもの**：Ch(A) で豊穣された圏と豊穣関手そのもの：Hom 複体、次数つき射と合成、Z⁰ と H⁰、dg 関手、dg 圏のテンソル積、自由 dg 圏、表示符号、一対象 dg 圏としての dg 代数（統合した「dg 代数」の分）。

**入らないもの**：
- dg 圏上の加群（Dᵒᵖ → Ch(A) の dg 関手）とその Hom 複体・写像錐・K(D)・前三角性は「B/dg 加群」へ。
- dg 商、cell の貼り付け、cell 分解（cycle cover から始める自由 dg 圏 DGCategoryCycleCover.Source も）は「B/dg 商と cell 分解」へ。
- Hom 複体の係数拡大・制限で作る dg 圏は「B/係数の取り替え」へ。
- dg 神経そのものは「C/dg 神経」へ。dg 圏の dg 神経を導来圏の模型として使うものは「D/導来 ∞ 圏」へ。
- dg 代数の胞体分解・path 対象・ホモトピー引き戻し・写像空間は「B/dg 代数のホモトピー論」へ。
- 豊穣圏の一般論（複体が主張に現れないもの）は「Z/豊穣圏」へ。

**小概念**：
- Z⁰ と H⁰
- dg 圏のテンソル積
- dg 圏の表示符号
- dg 圏（Hom 複体・次数つき射・合成）
- dg 関手
- 一対象 dg 圏としての dg 代数
- 自由 dg 圏

**文献**：
- HA §7.1.1（ファイルの場所による）

## B 複体と dg 圏/三角圏と t 構造

**入るもの**：三角圏の一般論：三角形、シフト、三角部分圏と厚い部分圏、Verdier 商、局所化、t 構造。主張に現れるのが一般の三角圏だけの宣言。

**入らないもの**：
- 複体のホモトピー圏・導来圏についての補題は「B/複体」へ。
- D(D)・Perf を三角圏として扱うものは「B/導来圏と Perf（dg 加群）」へ。
- 安定 ∞ 圏のホモトピー圏の三角構造は「D/安定 ∞ 圏」へ。∞ 圏の Verdier 列は「D/Verdier 列」へ。
- 加法圏・アーベル圏だけの話は「Z/圏・関手・極限」へ。

## B 複体と dg 圏/係数の取り替え

**入るもの**：環準同型 A → A′ に沿う底変換の関手が主語の宣言：複体・dg 圏・dg 加群の係数拡大と係数制限、導来係数拡大、それを Perf や dg 商の tria・Perf に誘導した関手。

**入らないもの**：
- dg 関手に沿う加群・双加群の制限（係数環は変えない）は「B/dg 加群」「B/双加群とテンソル」へ。
- 上に有界な導来圏の導来底変換（可換環論の側の定理）は「A/上に有界な導来圏と導来底変換」へ。
- E∞ 代数の係数変更は「F/E∞ 代数の圏（CAlg と加群）」へ。
- 底変換の関手が主語でなく、仮定に係数拡大が現れるだけの宣言は、主張の概念へ。

**小概念**：
- dg 商の係数変更
- dg 加群の係数変更
- dg 圏の係数変更
- 導来係数拡大
- 複体の係数拡大と係数制限

**文献**：小概念の reference に記載なし。

## B 複体と dg 圏/単体的鎖・Dold–Kan・シャッフル

**入るもの**：単体集合・単体的加群と鎖複体の間の対応：線形化と正規化（Moore）鎖複体・コチェイン、Dold–Kan の Γ と切断、Alexander–Whitney 写像、シャッフル（Eilenberg–Zilber）、単体的鎖のテンソル、線形化した区間ホモトピー。

**入らないもの**：
- Barratt–Eccles オペラドの shuffle 合成と、単体的鎖への全射オペラドの余作用（切断公式）は「F/Barratt–Eccles と全射オペラド」へ。
- 複体から Γ で作る Eilenberg–MacLane 空間とスペクトルの段は「G/Ω スペクトル（Bousfield–Friedlander）」へ。
- dg 神経の Hom 空間の計算は「C/dg 神経」へ（Dold–Kan の標準模型そのものはここ）。
- 余単体的可換環のコホモロジーと cup 積は「A/Čech 複体と被覆」へ。
- 単体集合だけの組合せ論（面・退化）は「C/単体集合（基本）」へ。鎖複体の添字の取り替えは「B/複体」へ。

**小概念**：
- Alexander–Whitney 写像と余代数構造
- シャッフル
- 整数加群・単体的加群・鎖複体のテンソル
- 線形化した区間ホモトピーと厳密化
- 線形化と正規化鎖複体
- 単体的環の正規化コチェインの係数（ULift ℤ） — 印：補助
- Dold–Kan 対応と正規化

**文献**：
- Berger–Fresse §1.1.4；KST Construction A.5
- Berger–Fresse §1.1.3；KST A.5
- KST Definition A.3、A.5
- KST Definition A.3、Construction A.5
- Berger–Fresse §1.1.4；KST Appendix A、Definition A.3
- Dold–Kan; HA 1.2.3

## B 複体と dg 圏/双加群とテンソル

**入るもの**：dg 双加群と、それに沿うテンソル：balanced テンソル積 M ⊗_D N、双加群の合成（相対テンソル）と結合・単位同型、制限、K-flat 性と K-flat 分解、導来双加群圏と導来合成、kernel（双加群）による D(D) → D(E) の導来作用。

**入らないもの**：
- 片側だけの dg 加群は「B/dg 加群」へ。
- 複体どうしのテンソル積は「B/複体」へ。dg 圏のテンソル積 Bᵒᵖ⊗C そのものは「B/dg 圏と dg 関手」へ。
- 双加群に沿う dg 圏の貼り合わせは「D/dg の貼り合わせ」へ。Land–Tamme の ⊙ の dg 模型は「H/lax 引き戻しと局所化不変量」へ。
- 相対 K-flat 加群の dg 神経と kernel の作用の ∞ 圏版は「D/導来 ∞ 圏」へ。
- モノイダル圏の中の双加群（Bimod）の一般論は「Z/モノイダル圏の中の加群」へ。
- 環準同型に沿う係数拡大は「B/係数の取り替え」へ。

**小概念**：
- Bᵒᵖ⊗C 上の加群としての双加群と半自由分解
- K-flat 性と K-flat 分解
- balanced テンソル積 M ⊗_D N
- dg 双加群（対象・値・閉零圏）
- kernel の導来作用
- 双加群の制限
- 双加群の合成（相対テンソル）
- 合成の結合同型と単位同型
- 導来双加群圏と導来合成
- 導来合成と制限の両立

**文献**：
- Keller §6.1
- Spaltenstein; Toën（dg 圏のテンソルの導来）
- Keller §6.1; Kelly（豊穣 coend）
- Toën, Morita 理論
- Keller §6; Toën §6

## B 複体と dg 圏/導来圏と Perf（dg 加群）

**入るもの**：dg 圏 D 上の導来圏 D(D)（擬同型による局所化）と Perf を三角圏として扱う宣言：局所化関手、有限 cell 対象と tria(D)、perfect 対象、Perf の Verdier 商、Perf の dg 増強、dg 関手・準同値・Morita 同値による Perf の関手性。

**入らないもの**：
- K(D)・擬同型の定義・ホモトピー射影性など局所化の前の水準は「B/dg 加群」へ。
- dg 神経による ∞ 圏の模型（Perf の ∞ 圏模型、dg 米田）は「D/導来 ∞ 圏」へ。小さい Perf の模型を K 理論の入力に束ねたものは「H/S 構成の入力（安定モデル・小さい Perf）」へ。
- 係数拡大の Perf への制限は「B/係数の取り替え」へ。双加群（kernel）の導来作用は「B/双加群とテンソル」へ。
- dg 商の tria・Perf と Verdier 商の比較は「B/dg 商と cell 分解」へ。
- 環上の狭義 perfect 複体と K₀ は「A/完全複体と K₀」へ。Mathlib の D(Mod_R) は「B/複体」へ。
- 安定 ∞ 圏の Verdier 列は「D/Verdier 列」へ。

**小概念**：
- Perf の Verdier 商
- Perf の dg 増強（射影的 perfect dg 加群）
- Perf の関手性と Morita 同値（自己準同型 dg 代数）
- Perf(D)（perfect 対象）
- 導来圏 D(D)（擬同型による局所化）
- 有限 cell 対象と tria(D)

**文献**：
- Verdier; Keller
- Keller §4.3, §6（Morita）
- Keller §5.3; Toën–Vaquié
- Keller, Deriving DG categories §4
- Keller §5; Toën

## B 複体と dg 圏/複体

**入るもの**：整数添字の余鎖複体・ℕ 添字の鎖複体そのものについての宣言：Hom 複体、テンソル積、写像錐、二重複体と全複体、極限・余極限、ホモロジーと分解、複体のホモトピー圏 K と導来圏 D(Mod_R)（Mathlib の三角圏としての補題）、複体の図式のホモトピー極限の模型。

**入らないもの**：
- 環準同型に沿った係数拡大・係数制限の関手は「B/係数の取り替え」へ。
- 単体的対象の正規化鎖・Dold–Kan の Γ・Alexander–Whitney・シャッフルは「B/単体的鎖・Dold–Kan・シャッフル」へ。
- 三角圏の一般論（複体が主張に現れないもの）は「B/三角圏と t 構造」へ。
- 複体の dg 神経 N_dg(Ch) の中の写像空間・fiber 四角形・cofiber 四角形、semifree 複体の dg 神経は「D/導来 ∞ 圏」へ。
- K-flat な複体は（決定どおり）「B/双加群とテンソル」の「K-flat 性と K-flat 分解」へ。
- Koszul 複体・de Rham 複体・Čech 複体・台つきの複体・狭義 perfect 複体は A のそれぞれの概念へ。上に有界な導来圏と導来底変換は「A/上に有界な導来圏と導来底変換」へ。
- 図式のモデル構造の一般論（複体が主張に現れないもの）は「E/図式のモデル構造とホモトピー余極限」「E/ホモトピー関数複体と分解」へ。

**小概念**：
- 複体のテンソル積と積構造
- 複体の図式のホモトピー極限（frame・重みつき end/coend）
- ホモロジー・分解・K-射影的複体
- 二重複体と全複体
- 写像錐と冪等な鎖写像の像
- 複体のホモトピー圏と導来圏
- 複体の極限・余極限と図式
- 複体（基本）と Hom 複体
- 鎖複体と添字の取り替え（埋め込み・切断）
- 複体の有限族のテンソル積と並べ替え

**文献**：
- Hovey §5
- Spaltenstein; Mathlib ProjectiveResolution
- Mathlib DerivedCategory
- Mathlib CochainComplex / HomComplex
- Berger–Moerdijk §1；Berger–Fresse §3.1
