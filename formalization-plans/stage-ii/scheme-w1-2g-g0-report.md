# SC-W1 G0：付値判定と有限族・一射の橋の最初の区切り

2026-11-14。数学・登録コミット **`ed170c16c`**。停止点 2f 後、承認された G0 の入口の束を検証した。**2g-1／2g-2 の停止点の完成報告ではない。** G1 以降の Lean は未着手。

## 1. 検証済みの範囲

任意の階数の付値環への写像を、忠実平坦な付値整域の拡大へ持ち上げるという affine v 被覆の述語を作った。有限族の述語は drafts/A6/ArcSheafProperty.lean の `ValuativeCoverFamily (fun _ => True)` と同じ量化・証人の形とし、一射の述語は BS 側の `IsAffineVCover` と同じ量化を使う。既存の宣言の型・名前を変更せず、AG から BS・KST・InfinityCategories・drafts を import していない。

有限族の v 判定が積への環準同型の v 判定と同値であることを証明した。逆向きには、有限積から整域への環準同型が一つの射影を経由することを証明した。Mathlib の有限積の素スペクトルの分解を使い、独自の冪等元の理論を作っていない。

合成・細分・一点族・切断の法則、および実際の pushout による任意の affine 底変換での保存も検証した。底変換の射に平坦性は課していない。付値判定から素スペクトルの全射性を得る向きだけを証明し、全射性が v 被覆性を意味するとはしていない。零環上での空虚な判定と、非零環上の有限 v 被覆族が空でないことも含む。

## 2. 型つきの宣言一覧

全て `SerrePositivity.AlgebraicGeometry`。以下は一行の主張で、**全 19 宣言の型・定義式・共通文脈は [型つき一覧](scheme-w1-2g-g0-types.md)** に記録した。

| 宣言 | 主張 |
| --- | --- |
| `IsAffineVCover` | 一射の affine v 被覆の付値判定。 |
| `ValuativeCoverFamily` | 階数条件を指定した有限族の付値判定。 |
| `IsAffineVCoverFamily` | 階数制限を置かない有限族の v 被覆。 |
| `isAffineVCover_of_retraction` | 切断を持つ環準同型は v 被覆。 |
| `isAffineVCover_id` | 恒等写像は v 被覆。 |
| `IsAffineVCover.comp` | v 被覆の合成は v 被覆。 |
| `IsAffineVCover.of_comp` | v 被覆である合成による細分から元の射の v 判定を得る。 |
| `exists_factor_evalRingHom_of_isDomain` | 有限積から整域への環準同型は一つの射影を経由。 |
| `isAffineVCoverFamily_iff_pi` | 有限族の v 判定と、積への一射の v 判定の同値。 |
| `isAffineVCoverFamily_of_member` | 一つの成分が v 被覆なら族全体も v 被覆。 |
| `IsAffineVCoverFamily.of_refinement` | 有限族の細分から元の族の v 判定を得る。 |
| `IsAffineVCoverFamily.comp` | 各成分の有限 v 被覆族との合成族は v 被覆。 |
| `IsAffineVCover.baseChange` | 実際の環の pushout による v 判定の保存。 |
| `IsAffineVCoverFamily.baseChange` | 各成分の実際の pushout による有限族の v 判定の保存。 |
| `isAffineVCoverFamily_punit_iff` | 一点族の判定と一射の判定の同値。 |
| `IsAffineVCover.surjectiveSpectrum` | v 判定から Spec 上の全射性。 |
| `isAffineVCover_of_subsingleton` | 零環からの射は付値判定を空虚に満たす。 |
| `isAffineVCoverFamily_of_subsingleton` | 零環上は空の族を含め任意の有限族が v 判定を満たす。 |
| `IsAffineVCoverFamily.nonempty` | 非零の基底環の有限 v 被覆族は空でない。 |

11-14 の新しい規則を反映し、既存構成の合成・係数移送・自然性などの法則に本数制限を置いていない。今回、単独で 200 行を超える構成・定理・証明分割はない。最長のファイルも 74 行。新しい構成・主定理・まとまりの外・外枠に届くときは従来どおり報告する。

## 3. 検証と規模

- 新規六モジュール、**本体 314 行、入口追加 12 行、合計 326 行**。ソースに明示した宣言は 19 件。
- 全六モジュールを `SerrePositivity/AlgebraicGeometry.lean` に直接登録。
- 対象と直接 importer：`lake build SerrePositivity.AlgebraicGeometry`、**4,786 jobs 成功**。
- 別実行の標準監査：`lake env lean scripts/audit_kst_scheme_lemmas.lean`、**10,661 宣言・標準三公理 propext、Classical.choice、Quot.sound のみ**。
- 個別の束は basic/family 2,267 jobs、pushout 2,266 jobs、Spec と族の底変換 2,270 jobs 成功。入口の集計は依存を含み、新規モジュール数とは異なる。
- 共有 `with_build_lock.sh --wait 3600` を各ビルド・監査の実行中だけ取得。監査の整理券は一つで待った。heartbeat・再帰・探索上限の引き上げ、sorry・admit・新しい公理はない。
- `git diff --check` 成功。main は凍結中のため取り込まず、math/scheme にだけコミットした。

## 4. 並べて行った紙の比較

[Rydh 3.10 と 3.12 の比較](scheme-w1-2g-rydh-route-comparison.md) に、最終主張を保った複体の筋、G1・G2 の変化、G3〜G5 の変化、停止点別の規模を記録した。

**比較の結論**：3.10 の fppf–proper 細分でも、同じ BS17 Thm 4.1(i) の affine 完全環の有限族の増大 Čech 完全性へ到達できる。3.12 のための準切断・open–finite 細分を省けるが、固有性と全射性を同じ有限型 F_p 段へ降ろす模型は残る。fppf の flatness のモデル化の費用も要る。

見積もりは **2g-1 約 9,000〜18,000 行、2g-2 約 5,700〜12,500 行、G0 込みの 2g 合計約 15,500〜32,300 行**。2h まで約 17,500〜37,300 行。推奨案は 3.10 経路だが、大幅な規模削減を保証する提案ではない。G1 以降の経路と外枠は調整役が判断する。

## 5. 残りと次の範囲

この束は G0 の「述語、有限族・一射、基本的な保存則」の区切りである。一般の faithfully flat 射・固有全射から付値判定を供給する十分性、試験付値環の宇宙を移す橋、スキームの v 判定・universally subtrusive 性との比較はまだ今回の本体に含まない。既存の `IsProper.eq_valuativeCriterion` や付値拡大の材料を使う必要があり、完成扱いにしない。

Rydh の構造定理・被覆模型を追加仮定として最終出力に残す案も採っていない。G1・G2 の幾何を 2g-1、G3〜G5 の判定と移送を 2g-2 とする新しい区切りを、以後の報告に使う。

## 次の束の型つき一覧（着手前、2026-11-14）

3.10 経路の承認を受け、G0 の残りの最初の束を以下に定める。以下はこの追記時点では未検証の型案であり、対象ビルド後に結果を追記する。既存 API の型は変えない。

1. `exists_valuationSubring_factor_of_injective_local_base`：V は付値整域、R は局所環、K は体、a:V→R は局所準同型、f:R→K に対し f∘a が単射なら、K の付値部分環 W と局所準同型 b:R→W が存在し、W→K∘b=f、b∘a は忠実平坦。
2. `exists_valuationSubring_extension_of_injective`：付値整域 V から体 K への単射 i は、K の付値部分環 W を経由し、V→W は忠実平坦。1 の a=id で得る。
3. `isAffineVCover_of_surjective_of_nil_kernel`：f:A→B が全射で ker(f)≤nilradical A なら IsAffineVCover f。試験付値整域への射が nil な核を消すので、同じ試験環へ持ち上げる。
4. `isAffineVCover_quotient_of_le_nilradical`：J≤nilradical A なら IsAffineVCover (Ideal.Quotient.mk J)。3 の商への特殊化。

1・2 は一般の flat／proper の十分性に必要な付値環拡大を供給する。3・4 は nilimmersion の付値判定を供給する。どちらも G0 の付値判定の束の中であり、Rydh の細分や模型を存在の仮定で代用しない。法則・特殊化・証明分割は本数で区切らず、200 行を超えれば行数も追記する。

3.10 の採用と外枠の変更：G1・G2 の 2g-1 は **25,000 行**、約 **12,000 行**で止まらず途中報告。2g-2 の外枠は 2g-1 の実測後に決める。G0 の残りの後は G1、G2 と続け、停止点 2g-1 では報告して G3 へ進む。main の凍結は継続し、自分の枝だけにコミットする。

### 続く束の型つき一覧（着手前）

- `exists_valuation_lift_of_faithfullyFlat`：V が付値整域、f:V→B が忠実平坦なら、付値整域 W、e:V→W、l:B→W が存在し、e は忠実平坦、l∘f=e。閉点上の素点から flat going-down で一般点上の素点を選び、その剰余体を前の付値部分環の因子化へ渡す。
- `isAffineVCover_of_faithfullyFlat`：任意の環準同型 f:A→B が忠実平坦なら IsAffineVCover f。任意の A→V でテンソル積へ底変換し、前の持ち上げを適用する。

この束も G0 の付値持ち上げの十分性であり、有限表示は要求しない。局所化と剰余体の間の式、テンソル積の可換式などの法則は同じ報告に型を追記して使う。

### スキーム側の付値判定の束（着手前の型）

- `IsSchemeVCover (f : X ⟶ Y)`：任意の付値整域 V と k:Spec V→Y に対し、付値整域 W、忠実平坦 e:V→W、l:Spec W→X があり、l≫f=Spec(e)≫k。
- `isSchemeVCover_specMap_iff (f : A→B)`：IsSchemeVCover (Spec.map f) ↔ IsAffineVCover f。Spec の完全忠実性で同じ環準同型へ戻す。
- `isSchemeVCover_of_proper_surjective (f : X→Y)`：f が固有・全射なら IsSchemeVCover f。試験付値環の分数体上のファイバーの点を取り、残留体への付値拡大と固有性の付値判定で持ち上げる。始域・終域の affine 性は要求しない。

この構成に伴う Spec の合成則・pullback の可換式・環とスキームの量化の移送は本数を区切らず型を記録する。G1 の Rydh の細分自体にはまだ着手しない。

スキーム側の同じ構成の法則として、`IsSchemeVCover.comp`（g と f の v 判定から f≫g の判定）、`IsSchemeVCover.of_comp`（f≫g の判定から g の判定）、`IsSchemeVCover.baseChange`（実際の Cartesian square の pullback への保存）を供給する。これらは定義済みの付値持ち上げの合成・普遍性の法則であり、別の幾何学的構造定理は加えない。

付随する点の法則 `IsSchemeVCover.surjective` は、上の付値判定を各点の剰余体で試して元のスキームの射の全射性を返す型で供給する。特に `IsSchemeVCover.baseChange` と組み合わせれば全ての底変換後の全射性を得る。


## 2026-11-14：付値持ち上げの束の検証結果

数学 `5fb95d17b`（付値拡大・nil・忠実平坦、四ファイル 180 行）と `d902118ed`（スキームの判定・固有全射・合成と底変換・全射性、四ファイル 188 行）を検証した。

- 局所環の体への射を支配する付値部分環の構成を使い、付値基底への射が単射なら拡大が忠実平坦となる。
- 忠実平坦射の付値持ち上げは、閉点上の素点を取った後、flat going-down で一般点上の素点を選び、その剰余体を同じ付値部分環の構成へ渡した。有限表示・Noether 性は要求しない。
- 固有全射は分数体上のファイバーの点とその剰余体を使い、付値拡大後に Mathlib の固有性の付値判定を適用した。元のスキームの affine 性を要求していない。
- 環側とスキーム側の判定は `isSchemeVCover_specMap_iff` で同値。スキーム側の合成・細分・Cartesian な底変換と全射性も閉じた。

新しい八モジュールを入口に登録して `lake build SerrePositivity.AlgebraicGeometry` **4,796 jobs 成功**。別実行の標準監査は **10,676 宣言・標準三公理のみ**。共有鍵 `--wait 3600`、待ちは一つ、実行中だけ保持した。計算上限の引き上げ・sorry・admit・新しい公理はない。

G0 累計は **14 新規モジュール・本体 682 行、入口追加 28 行、合計 710 行**。各宣言の型は型つき一覧へ追加した。200 行を超える単独の宣言・証明分割はない。前記 §5 に未実装と記した nil・忠実平坦・固有全射の十分性とスキーム側の橋は今回供給済み。任意の別宇宙の付値試験への移送の一般定理は作っていないが、既存利用側と同じ宇宙の試験を持つ今回の型は保持しており、最終出力を狭めていない。別宇宙の入口が必要になれば、その実際の型を一覧に追加して供給する。

次の G1 は [2g-1 の実装記録](scheme-w1-2g-1-report.md) の着手前の型つき一覧に従い、特殊化の付値環による実現と、v 判定から特殊化の鎖の持ち上げへの接続から始める。2g-1 自体は未完である。
