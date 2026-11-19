# BC-W1　BS の整理の段 0

**現在地　段 0 の報告。** `research/cited-coverage` で `git merge main` により `cbcb40a59` を取り込んだ。対象の Lean・対応表・監査一覧をこのコミットで固定した。確認時の後続 main `e6b608c4f` までの差分は引き継ぎ・移転の文書2本と調整役用スクリプト3本。Lean の変更・ビルド・鍵の使用は0件。

**一覧：済み 33／全体 33（うち追加 0）**。指示書に列挙された32件と、範囲に明記された既存の BR26′。済みは段 0 での再照合を指す。実施済み5、一部16、未実施9、前提が変わった3。[項目表](../../../research/bs-cleanup-w1/items.csv)

移動と層の旧案の大半は実施済み。残る全ファイルの移動候補は `DiscreteDelta` 1本で、公開名二つを保つ。BS の885本すべてが三根の合併から届く。監査だけから届く `TorCriteria` は132行。B・C で小さい候補は、同型に沿う perfectoid 化の前合成の二重証明と、Frobenius が δ 射であることの三版。

## 1. 項目の現状と分類

| 区分 | 今回の範囲 | 扱い |
| --- | --- | --- |
| A 移動・改名 | BR14、BR19、BR32、BR42、BR5・23・26′・39・41・43 の配置や改名部分 | BR14・19・32・42 は現行パスへ実施済み。BR5・23・41 のファイル内抽出は依存を分離する作業を含む。BR39・43 は型を判別してから名前を扱う。 |
| B 重複の一本化 | BR4〜7、BR10、BR12、BR15、BR18、BR35〜39、BR44、BR22・23 の模型や互換口 | 現行の署名と名前の利用先は型の表。原典に近い一般の形を残し、旧来の特殊化は署名・指定写像を保った系にできる範囲で扱う。 |
| C 証明の共用・言い換え | BR13、BR16〜17、BR21〜24、BR29、BR40、BR41 の抽出部分 | 落とせない仮定・係数脚は境界欄に記載。BR16 の閉じた削除案は判断材料、BR17 の単射性は個別候補。 |
| D 文書 | BR25・BR34、BR19・24・43 の文書部分 | 工程ラベルや古い置き場所の文を数学的内容と原典の番号に直す。 |
| 到達の調査 | BR8 | 閉包と使用箇所を記録。処遇の確定は利用・原典・監査を照合してから。 |

BR25 の先頭モジュール文書には概要見出しが866／885本。工程ラベルの字句候補は10本24行。11-12 は概要590／604本、工程ラベル33本と報告しており、後のファイル分割で母集団が変わった。BR34 の六組では、`DeltaLocalization` の使われ方は §2.15・Ex 2.21 に更新済み。`FreeDeltaFrobeniusFlat` は §2.36・§2.44 の用途を記載し、`CrystallineTensorRegularity` が直接 import する。`AndreFlatness` は Tower による公開入口と、第二文の根の供給を明記済み。旧工程名 A1 の説明は数学的な名に換えられる。`Surjectivity` 491〜498行には自分自身への誘導と重複が残る。`PerfectoidAlmost` の概要は conormal と冪等性を記載し、一般の §10.4 との違いを明示済み。旧 `Derived/Interface` は `Interface/Derived` 等に分かれ、`IntegralExistence` の初期図式・単位の説明を分離後の各ファイルと照合した。生成された引用属性の文言はこの文書作業の対象と区別する。[文書候補](../../../research/bs-cleanup-w1/docstrings.csv)

## 2. A の移動案

`Semiperfectoid/Discrete/DiscreteDelta.lean` から `Delta/Basic/DiscreteDelta.lean` へ。Lemma 7.7(1) の比較を構成する二つの古典的な δ 構造の一意性で、内容は Remark 2.2 側の一般論。ファイルの依存は δ 環の基本、Mathlib の正則性、引用属性。§7 の prism 構成はこの部品を利用する側に残す。対応表の §7.7 は現状 `none` で、宣言2件が記録されている。移動ではこの分類を維持する。[移動表](../../../research/bs-cleanup-w1/moves.csv)・[§7.7](../../../research/bs-coverage/review/ch7.csv#L8)

BR14 の正式監査4本は `scripts/audit/bs_power_root_envelope/` に移動済み。BR19 の `PrismaticResidue` は DerivedCompletion、`PerfectDeltaResidue` は André、`PDCompletionPrism` は §7.2、Thm 3.10 の比較の芯は `Prism/Perfectoid`。BR32 の一般分冪は `CommutativeAlgebra/DividedPowers`、有限正則列の系列は `Delta/DividedPower/RegularSequence`、Def 2.42 は `Delta/CompleteRegularity`。BR42 は `SurjectiveQuotientPerfectoidization` に改名済みで、定義本体の `Perfectoidization` と分離した。

BR5 の Lemma 2.32 節の分離、BR23 の環同型による輸送の切り出し、BR41 の残る比較は、それぞれファイルの一部を動かす候補。純移動の一束に加えず、利用する定理と依存の向きを確かめてから別に扱う。

## 3. 型つきの B・C と確認が要る境界

[型つき一覧](../../../research/bs-cleanup-w1/signatures.csv) は既存署名、定義元、利用候補ファイル数を記録した。[行数の見込み](../../../research/bs-cleanup-w1/estimates.csv) は作業対象の範囲を明示する。素は835〜1,735行、[調整 §2.1](../../coordination.md#21-lean-の作業の進め方標準2026-11-17-ユーザー決定⑥-sc-w1-の進め方を標準にする)の係数2で1,670〜3,470行。余裕3%を各束の上限に加えた候補の合計は3,582行。旧証明の置換候補行は純減の計算に使わない。既存ファイルの移動行数、定理を新たに形式化する行数、Archive の候補はこの工数から外した。

| 束 | 残す形と署名上の決め手 |
| --- | --- |
| BR4・BR5 | `relativeFreeDeltaStructure` と `existsUnique_relativeFreeDeltaHom` は一般の基底 δ 環。ℤ 版の定義式を維持し、比較定理経由で既存証明を共有する。`isDeltaHom_frobeniusLift_general` は p 倍の単射性を仮定せず同じ結論を返す。先に `RelativeFreeDelta` の `p_mul_delta_dvd_delta_pow` への依存を分離する。 |
| BR6・BR38 | `dpFamilyFactorialEquiv` は有限族と係数代数を指定し、`principalDPFactorialEquiv` は一元と環同型を指定する。共通部は局所化への単射と指定した像による同型の構成。各同型の定義と係数脚の計算則を維持する。 |
| BR7・BR10・BR35 | 一元版は両方とも指定された正次数 monic 多項式に対する根・元環からの射・p 完全忠実平坦性。族版では `exists_monicFamilyRootedPerfectoidExtension` が任意添字の同じ結論を供給する。Tower と二つの Variants の定義元は現行の import 閉包で相互に到達しない。公開口から Tower へ向ける辺はこの組の循環を作らない。Variants の保存決定に従い公開口は残す。 |
| BR12・BR13 | 全射性の定理と存在定理を区別する。H⁰ の6例は入力の余極限・有限性・支持の条件が異なるので、既存の H⁰ 同型を指定模型の同型へ渡す証明末尾から共用する。prism 表示の旧試験は Fontaine 脚を使う場合がある。単に商との同型の存在で十分な呼び側だけを `exists_boundedPerfectPrismPresentation` へ移せる。 |
| BR15・BR17 | `existsUnique_classicalPrismPerfectionHom` と PD 完備化版の標的条件・可換条件を旧版と比較する。商写像からの単射性の二証明は生成元の選択が異なる。共用するなら反復除算で得る (xin (d)^n) と分離性を引数にし、商射の同定は呼び側へ残す。p 非単元は非零と完備性が仮定。 |
| BR21 | `comp_ringEquiv` と `precomp_ringEquiv` は、型を読むとどちらも始域の同型による前合成。後合成の一般化とは別。`lift_unique` を使って標的 perfectoid 環への二つの射が元環上で等しければ等しいという補題を証明できる。 |
| BR22・BR23 | Witt 余積経路の mod p と、完備テンソルの H⁰ 版の完備性・代数脚を区別する。指定三角形の等式だけを共用する案。環版の §8.13 の入口は `prop813CompletedTensorMap_isPerfectoidization`。WittPushout の互換名は共通層の宣言を alias で参照するので、互換口の処遇は利用先の確認後。 |
| BR24 | 元環 R の作用による `IsAlmostIso I f` は、既存の線形写像の核と余核に対して使う。`IsAlmostInjective.iff_smul_eq_zero` と全射からの `IsAlmostSurjective.of_surjective` が既存。所与のスカラー作用との一致と元の全射性を維持。 |
| BR29・BR36・BR37 | Thm 3.10 は対象の表示・Witt 比較・Ainf 比較まで既存。BR36 は step を仮定する版、無仮定版、無仮定版を呼ぶ `Inputs` の公開入口の三つ。BR37 の一般版は完全平坦。ℤ 版の完全忠実平坦性を保持するには忠実性の既存証明が要る。 |
| BR39・BR40・BR43 | 同名でも、frame と presentation の二つの余積では指定脚が異なり、Arc と dg の `baseExtension` は型が異なる。有限・整・E3 を仮定する三つの入口を区別する。5∞-0 で草稿 A0・A1 の Tor 振幅は本体へ追従した。D77 の観察どおり、草稿の原典仮定 `Construction61Hypotheses` と本体の二入力の型は別に維持する。単項の `perfectoidIdeal` と一般イデアルの商の `perfectoidKernel` は比較を伴う。 |
| BR18・BR44 | テンソル枝と剛性の定義は、到達と個別の型の利用と原典との対応を区別して判断する。とくに剛性の二つは本体の別ファイルに短名の使用がなく、正式監査と BS §1.5・§3.5 の記録がある。 |

### 既存補題から出す署名の候補

次の二つは既存の構成・法則に対する形の案。前者は `lift_unique` を二度適用する。後者は同じ R 線形写像について `IsAlmostInjective` と `IsAlmostSurjective` を組み合わせる。

```lean
theorem IsPerfectoidization.hom_ext
    {S C D : Type u} [CommRing S] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) (hD : IsIntegralPerfectoid D p)
    {g h : C →+* D} (e : g.comp f = h.comp f) : g = h

theorem isAlmostIso_of_surjective_of_smul_eq_zero
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hk : ∀ a ∈ I, ∀ x : M, f x = 0 → a • x = 0) :
    IsAlmostIso I f
```

### 別の仕事になる比較

- BR4 の整数の始性と Ex 2.6 の残存主張、BR6・BR7 で既存比較が不足する場合の指定脚を保つ新しい同型、BR15 の完備化模型の必要な比較は、それぞれ型を確定してから再見積もりする。
- BR22・BR23 の一般の導来模型の同一視、BR29 の圏同値と A5 site の同値、BR36 の A9 における E3 の処理、BR43 に関連する一般の J と単項の系列の橋（BR53）は段 0 の工数の外。site・RΓ・envelope の原典の定義と `BhattScholze/Inputs/` の引用の型はどの束でも維持する。

## 4. BR8 の三根

| 到達元 | 11-12 本／行 | 現行 本／行 |
| --- | ---: | ---: |
| root・入口・sorry 対象の所在 | 593／165,353 | 884／189,017 |
| 対応表の own・partial・interface | 7／2,619 | 302／125,408 |
| 正式監査 | 604／171,356 | 885／189,149 |
| 正式監査だけ | 11／6,003 | 1／132 |
| 三根のどれからも届かない | 0／0 | 0／0 |

現行の根は root 等59個、対応表の解決済みローカルファイル1,341個（BS は80個）、正式監査108本。11-12 の「集約からのみ、または全く import されない60本」は、三根の閉包外と異なる指標。11-12 の対応表由来の数は当時の表で解決できた参照で、監査経路により三根合併の結果を独立に確かめられる。現行の監査のみの `PerfectoidIdeal/TorCriteria.lean` は `scripts/audit/bhatt_scholze.lean` から直接 import があり、11-02 の保持決定もある。行数や到達元だけで削除候補にはしない。[各ファイルの経路](../../../research/bs-cleanup-w1/reachability.csv)・[根と照合方法](../../../research/bs-cleanup-w1/README.md)

## 5. 逆向きの層と相反する判断

- BR26′ の元の2辺は現行0。Koszul の `Powers` と KST の `UniversalRegularSequence` は共通の MonicRelation、`PrincipalCompletionUniformBound` は共通の完備化の比較を参照する。追跡済み CommutativeAlgebra・HomologicalAlgebra・KST の明示ヘッダーから BS への直接辺も0。AlgebraicGeometry の ArcRouteB の15辺・13本は §8 のモデルの利用で、同じ逆向き基盤として数えない。
- BR41 の当初の3辺は0。CrystallineTensorRegularity は Delta、除算の単射性は PDivision/Injectivity、完備化の座標比較は PDCompletionCoordinates にある。R2-1 の KST への依存も ScalarTensorView の共通層へ移った。
- 追加の R3-2・R7-3・R10-5 の照合では、細分した §7.2→§7.3 の直接 import が2辺残る。`LciEnvelopePresentation` → `Andre.Envelope.DivisionResidue` は Delta の `AdjoinResidue` と André の `Normalized` を接ぐ比較。`PDCompletionPrism` → `Andre.Transfinite.Colimit` は両者が §7 に移った後の辺。`PDCompletionPrism.lean:67` の `completedUnit_pure_bounded_torsion` は `HomologicalAlgebra/DerivedCompletion/PrincipalCompletionComparisons.lean:264` が現在の定義元。宣言名を保ったまま直接 import を共通基盤へ狭める候補。DivisionResidue は Lci 側が `deltaAdjoinDivisionResidueBaseMap` と同じ剰余上の忠実平坦性を指定するので、既存の比較のうち下へ出せる部分を型で選ぶ。台帳にある辺と現在の行は [層の表](../../../research/bs-cleanup-w1/layers.csv)。
- BR16 の旧案は正則版の枝を削り、単射性だけを抽出する案。10-30 の決定は、`wittRegularQuotientFontaineMap_surjective`・`_bijective` の `IsHausdorff (ker θ)` を供給する Fontaine 核の分離性の連鎖を保持するもの。監査が両者を検査する。両方の根拠を記録し、今回の適用案には正則版の処遇を入れない。[保持の記録](../../refactor-plan.md#L203)
- BR10 は旧重複の削除案と W8 の Variants 保持決定が交差する。BR35 は同じ型を維持して証明を呼び出し直すだけの候補とし、Variants の削除・Archive 案は採らない。BR14 は旧 B3 の retained より後の台帳決定を実施済み。

## 6. 影響と追従

| 調査 | 本体 | blueprint | scripts | BS drafts |
| --- | ---: | ---: | ---: | ---: |
| A の移動元 | 1 | 0 | 0 | 0 |
| A の明示 import の書き換え候補 | 2 | 0 | 1 | 0 |
| A の逆向き import 閉包（移動元含む） | 30 | 4 | 7 | 0 |
| B・C の署名の字句参照と定義元の候補 | 58 | 2 | 5 | 2 |

A の直接追従は `BhattScholze.lean`、`DiscretePrism.lean`、`scripts/audit_bhatt_scholze_stage2.lean`。対応表の直接参照は A が §7.7 の2宣言、B・C は6参照。B・C は別に `research/bs-w13-scratch/` に6本の参照候補がある。適用後は対応表の位置を引き直し、調整役が BS の生成物（`SerreBlueprint/BS/Section7.lean` に現行の二つの宣言名と原稿、部の `generated.json` に生成情報）とブループリント入口を作り直す。字句参照は短名の衝突を含むため、B・C のファイル数は確定した編集数より広い。[ファイル別影響](../../../research/bs-cleanup-w1/impact.csv)・[対応表の位置](../../../research/bs-cleanup-w1/coverage-impact.csv)

③-a の完了は基準 main の取り込み済み。⑥、③-b の停止点も同じ main の先祖で、作業木を作り直す必要はない。各最終取り込み系列で A の移動元の直接 import は0。⑥の既存差分と推移的に重なるのは集約の `SerrePositivity.lean`。⑥の ArcRouteB は BS §8 を利用するので、将来 BR22・23 の公開型の変更を含める場合は改めて確認する。IC-2 の紙（`a1fbde1af`）の移動元1,625本は、今回の A の移動元、B・C の型の所在と直接重ならない。現行の IC 枝 `6680433e4` は main を取り込んだ状態で、紙の移動表に差分がない。[枝の照合](../../../research/bs-cleanup-w1/branch-impact.json)

## 7. 実施する場合の順序と時間

IC-2 の後を前提とする。以下は適用を承認された後の見込みで、待機時間は含めない。

| 順 | 一束の内容 | 適用の見込み | 束の検証の見込み |
| --- | --- | ---: | ---: |
| 1 | A 全体。DiscreteDelta を名前を保って移し、直接 import と参照位置を更新 | 0.5〜1時間 | 0.5〜1.5時間。静的なパス・閉包・重複確認、対象と直結する監査、保存比較 |
| 2 | BR5・BR37 と循環を切る最小限の分離。続いて BR6・BR38 | 3〜7時間 | 1〜3時間。一般形・特殊化・局所化像の保存、§2 の監査 |
| 3 | BR4、BR7・BR10・BR12・BR13・BR35。prism 表示を使える旧証明から進行 | 4〜8時間 | 1〜3時間。完備性・忠実平坦性・指定射、§7 の監査 |
| 4 | BR15・BR17・BR29。証明だけを共用できる箇所 | 2〜5時間 | 1〜2時間。旧 §3.9・§3.10 と Fontaine の監査を維持 |
| 5 | BR21〜BR24 と残る BR41。BR40 の追従と D の文書は独立した差分 | 3〜7時間 | 1〜3時間。完備テンソル・almost の監査、旧名の参照先・草稿の再照合 |

BR18・BR39・BR44 の処遇は上の時間に含めない。各束の保存比較は型・公理・sorry の差を照合し、正式監査と root の全体検証を調整役がまとめる場合は別に4〜7時間を見込む。IC-1 の取り込み検証約6時間を全体検証の参照値とした。A は純移動1本、B・C は汎用層を切り出した場合に再ビルド範囲が増えるので、その時点で importer を取り直す。

## 8. 新しい候補

台帳に新番号を要する候補は今回追加しない。残った候補は既存 BR または節の見直しの内訳に位置づけた。以上を段 0 の停止点とする。
