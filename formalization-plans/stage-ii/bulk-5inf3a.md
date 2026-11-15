# 一括レーン：5∞-3a（HT 比較の古典の段）の指示

作成：2026-11-15（調整役）。B3′ の完了（60183b0f8）の後。段 0 は `report-bulk-w1.md`「5∞-3a 段0」（336942ab0）。

## 1. 承認

段 0 を承認する：HT01〜HT06、見込み 3,000〜7,000 行、4〜8 日。終点は draft と同じ型（`affineLine_moduleComparison`・`hodgeTate_iso`・`hodgeTate_iso_crystalline`、`HodgeTateIsoStatement P hP r` は古典の型）。
- **外枠 14,000 行**（上端の 2 倍）、約 7,000 行で止まらずに途中報告。型つきの一覧（HT01〜HT06）で止め、数え方は `coordination.md` §2。
- **HT02（Lemma 4.22 の鎖複体版、1,500〜3,000 行）が主な不確実性**。HT01・HT02 を最初の小さな束にし、既存の K-flat・完備化の API への接続を検査した時点で、止まらずに HT02 の実測と残りの見込みを報告する。
- 含めないもの（Cor 4.12 の CAlg 値、D27、非向き付き基底・étale 層、一般の E∞ 構造）はそのとおり。drafts の ∞ の型は古典の型に置き換えてよい（second-half 5∞-3a の行）。
- 原典との差（Cor 5.5 から Prop 6.2 (b) へ、ではなく一般 HT の系として Cor 5.5 を回収）は docstring に一行。一般 HT の証明に一般の結晶の入力を使って循環させない。
- 置き場所は `BhattScholze/Prismatic/HodgeTate/`（B3′ 後の配置）。新しい本は BS の stage II の監査に登録する案を報告に。

## 2. 規則

- 他のレーンの持ち分（EInfinity/・InfinityCategories/・AlgebraicGeometry/、drafts の ⑤a の P⁰）に書き込まない。drafts/A1 の該当宣言を本体へ昇格するときは、drafts の側を import で置き換える（5∞-0 と同じ）。
- 鍵は `--class bulk`、昼は 3〜5 分の塊。
- 5∞-3a の完成が停止点。報告して止まらずに 5∞-7a の段 0（紙）へ。
