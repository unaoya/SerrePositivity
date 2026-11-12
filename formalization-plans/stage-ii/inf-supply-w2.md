# Codex 指示書 IS-W2：∞ 供給 b — Δ・Δᵒᵖ の橋（G10 と幾何学的実現）

作成：2026-11-12（段階 II の調整役）。宛先：③-b ∞ 供給 b の Codex（⑤b のチャットを転用。BS-D69 停止点 3 の取り込みと KL-W1 の改名への追従の後に始める）。検収：調整役。決定：ユーザー（11-12、`stage-ii-second-half.md`）。正本：[段階 II 後半](stage-ii-second-half.md) の 3b-0〜3b-4、[入口表](../bhatt-scholze/foundation-entry-points.md) §4.1（G10 の依頼の型）、[IS-W1](inf-supply-w1.md) の追記（11-10、G10 の範囲）。

## 0. 目標

厳密な（1 圏の）単体的・余単体的図式のホモトピー余極限・極限（幾何学的実現、Tot）と、準圏の native な余極限・極限の錐を、**全関手の形で、射と指定錐まで**結ぶ。これが段階 II 後半の最長の経路の入口（A1 の HT 比較、A0 の Čech–Alexander、A2、⑤a の sifted・Tot がすべてこれを待つ）。

| 段 | 内容 | 使う側 |
| --- | --- | --- |
| 3b-1 | 厳密な Δᵒᵖ 図式（値は D(A) ＝ `derivedInfinityCategory A` の模型 Semifree 複体）の幾何学的実現と、D(A) の native な余極限の錐の橋。頂点・脚・射への自然性まで | ⑤a の sifted（忘却が幾何学的実現を保つ）、A2 |
| 3b-2 | **G10**：余単体的 A 加群（複体）の D(A) での Δ 上の極限は Tot（交代余面複体の積全複体）で計算される。入口表 §4.1 の `cosimplicialModule_limitCone` を、**X に関手的で、X の射と指定錐まで**比べる形にそろえる。各次数のホモロジーの同型は、錐の脚と標準射が両立する形 | A0（C^• が Δ を計算）、A1、A6 Prop 8.10、⑤a の Tot |
| 3b-3 | coherent な図式（`Δᵒᵖ`・`Δ` の nerve から D(A) への任意の射）を厳密な図式へ移す比較と、錐の輸送（両方向） | ⑤a の sifted（任意の sifted 形状へ延ばす前段）、A2 |
| 3b-4 | 値の一般化：(i) CAlg_A（Barratt–Eccles 模型の局所化。忘却 U との両立：U が実現・Tot を保つことを、⑤a が使える形で）、(ii) 点つき Kan 複体（L9 の `CosimplicialTotalization` の Tot が ∞ 極限であること） | ⑤a の `ofCosimplicial_cone`・sifted、A1、K の L9 |

**範囲の外**：任意の sifted 形状への延長（⑤a の 5a-4 で BE 固有部分と一緒に）、非有界な余単体的 cdga の全比較（IS-W1 追記 11-10）、G8・G14・G9（③-a）。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 既存の道具の洗い出しと型案：`HomotopyLimits/BousfieldKan*`（一般の小圏の Kan 値図式の coend が ∞ 余極限、coherent 版）、`HomotopicalAlgebra/Diagram/HomotopyColimit`（cofibrant 置換と比較）、`KST/Spectra/CosimplicialTotalization`（厳密な Tot と Reedy）、`EInfinity/BarrattEccles/DiagramModel`（projective 模型、hocolim の比較）、`F2/Presentable/SiftedColimitPreservation`（`PreservesSmallSiftedColimits` の型）、D(A) の dg nerve と Semifree 模型。3b-1〜3b-4 の各主張の型案（使う側の drafts の型に合わせる：`cosimplicialModule_limitCone`、`totEInfinity_isLimitCone`、`PreservesSmallSiftedColimits`）、証明の筋、不足、規模。**[ModelCategory SSet] を要求する既存の版は使わない**（使えそうな版が全部それなら報告） | **停止点 0**：調整役が確かめる |
| 段 1 | 3b-1 | 停止点 1 |
| 段 2 | 3b-2（G10、D(A) 値） | 停止点 2：**これだけで取り込んでよい**（A0・A1・A6 が待つ） |
| 段 3 | 3b-3 | 停止点 3 |
| 段 4 | 3b-4 | 停止点 4：IS-W2 の区切り |

- 停止点 0 は承認を待つ。段 1〜4 は「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。
- 使う側の drafts の型を変える必要があれば止める（drafts が原典や計画より強い主張を抱えていると分かったときも止めて報告。D76・D77 と同じ扱い）。
- 規模の上限は段 0 の見込みの 1.3 倍。超えそうなときは報告して止める。止まる前に、それまでの検証済みの分をコミットする。

## 2. 規則

1. 新しい数学は**新規ファイルだけ**。既存の宣言の本文・型・名前は変えない。
2. sorry・公理・新しい引用を残さない。`[ModelCategory SSet]` のような満たせない仮定を使わない。
3. 置き場所は KL-W1 の後の配置：一般の ∞ 圏の主張は `InfinityCategories/Kerodon/LimitsAndColimits/` の該当する節（README の節番号・Tag の表に従い、docstring に Kerodon の番号を書く）、HTT・HA 由来は `InfinityCategories/HTT/`・`HA/`、D(A) 固有は `InfinityCategories/HA/DerivedCategoryModels/` か `Project/DerivedCategories/`、CAlg 固有は `EInfinity/`。迷ったら報告に印を付けて `Project/` に置く（調整役が決める）。
4. 入口と監査への登録は調整役。docstring は日本語の 概要／方針／規約／使われ方 と文献の番号（HTT 4.2.4.1・A.3.3、HA 1.2.4、Kerodon の Tag）。
5. 主張は**全関手版**（対象ごとの同型で済ませない）。native な錐は指定された頂点・脚を持つ形で返し、「存在する」だけにしない。
6. ビルドの鍵は `with_build_lock.sh --wait 3600`、整理券は一枚、鍵はビルドの間だけ。main の作業木では編集もビルドもしない。枝は main から `math/inf-supply-b`（worktree は今の `../SerrePositivity-bs-d68` のままでよい）。報告は `stage-ii/report-inf-supply-w2.md`。
