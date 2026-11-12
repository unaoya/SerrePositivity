# BS 勉強ノートにあった「形式化の課題」の原文（2026-11-12）

`exposition/ja/bs/02-delta.html`・`03-prism.html` の「形式化の課題」の節（T2-n・T3-n、10-25〜11-07 に書いたもの）を、ノートから外す前に写したもの。文は変えていない。ユーザーの方針（11-12）で、作業項目もリファクタ候補と同じく形式化の側で管理し、扱いは形式化の調整役が判断する。**状態は確かめていない**（たとえば T2-1 の多変数化は BS-W15 K1、T3-3 の Ex 3.4 は BS-W15 K2 で入っている）。今の状態は地図 `research/bs-coverage/items.csv` と `formalization-plans/bhatt-scholze/design-status.md` を見る。

## 02-delta.html:399

どれも「導来 pushout が離散」という主張を含むので、離散な環と Koszul 正則性で言い直した形で足りるかを A0 の紙上設計で決める。その判断の前には Codex に渡さない。

- **T2-0**　一般のテンソル積への δ 構造（Rem 2.7）：δ 射 \(A\to B\)、\(A\to C\) について \(B\otimes_A C\) に両立する δ 構造（W₂ 切断のテンソル積）。A0 の prism の余積の土台。

- **T2-1**　Lemma 2.38 の離散版を r 個の列へ：\(r=1\)（`PrincipalDP*`）を多変数の分冪代数（一変数版 `RankOneDP*` のテンソル積）と Koszul 複体の帰納法で一般化し、pd 包が p ねじれなしで \(\bmod p\) で \(\mathrm{Kos}(B/p;f^p)\) 上自由であることを示す。

- **T2-2**　Cor 2.39 の一般形：\(A\{\varphi(f_i)/p\}\cong D_{(f)}(A)\)。Lemma 2.36 の多元版（像の形）は済なので、生の包が p ねじれなしであること（Lemma 2.11 の Frobenius の忠実平坦性から）と T2-1 を合わせる。

- **T2-3**　Def 2.42・Lemma 2.43・Cor 2.44 の離散版（`IsCompletelyFlat` を使う）。Prop 3.13 の一般形の入力。

- **T2-4**　Ex 2.21：普遍 distinguished δ 環（Lemma 2.15 の局所化と自由 δ 環から）。

## 03-prism.html:166

- **T3-1**　Lemma 3.6（単項の場合）：\(\varphi(d)\) が distinguished であること。

- **T3-2**　Lemma 3.7（有界 prism の性質）の (2)〜(4)。(1) と有界な標的への剛性は W7 で `Prism/Bounded/`・`Prism/PerfectPrismHomLift` に移したので、そこへ足す。

- **T3-3**　Ex 3.4：普遍向き付き prism（T2-4 の完備化）。

- **T3-4**　Prop 3.13 の一般形（向き付き・固定基底）。T2-0・T2-3 の後。

- **T3-5**　Lemma 3.5 の後半：δ 射 \(A\to B\) で \(B\) が導来 \((p,d)\) 完備かつ \(d\) の像が非零因子なら \((B,dB)\) は prism（A0 の Čech 脈体の各項を prism として扱うのに使う）。

