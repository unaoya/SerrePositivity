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
