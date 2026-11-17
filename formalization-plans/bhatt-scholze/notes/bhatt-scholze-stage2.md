# BS-0：E3 の文献入力を除くための第二段階調査

2026-10-25。読み取り調査と計画のみ。Lean ソース変更・ビルド・新規の未証明入力はなし。
対象は `SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`。
以下、宣言の `SerrePositivity.` を省略する。見積りは一人の実作業量（人週＝40時間）、
既存基盤を再利用する粗い計画値で、ビルド待ち・他レーンの工程は含めない。

## 0. 根拠と判定

- 指定された二計画、Inputs・Interface・共通 Perfectoidization・CLMST/Algebra とその利用先、
  解説 `par:bs-thm74`・`par:bs-andre`・`par:bs-cor812` を照合した。
- 原典：[BS 著者版](../../../paper/refs/BS-prisms-author.pdf) §7（pp.54–62）、§8（pp.63–70）、
  §10（pp.78–83）、必要な §4–6（pp.36–53）。
  CLMST は [手元の v4](../../../paper/refs/CLMST-2209.04046v4.pdf) §2.4・§4、特に
  Prop 2.4.7、Claim 2.4.8、Prop 2.4.9、Notation 4.0.1、Cor 4.0.4、Prop 4.0.14。
- `bhatt-scholze.md` §0 の「二入力」は旧状態。現行では旧二入口は E3 依存の定理。
  Cor 7.3・Thm 7.4・André・Lemma 10.3・Prop 8.13 環版は既存の証明を再利用する。
- **B は指定された証明済み部品だけで完結する代替証明にはならない。**
  semiperfectoid 商の存在・閉側・底変換は賄えるが、有限代数一般の存在と excision は残る。
  これは別証明の不存在定理ではなく、CLMST の証明を追った際に閉じない論理的な箇所の判定。
- **E3 自体の除去には A を推奨する。** 主定理からだけ E3 を外す狭い目標と、
  全通常代数上の E3 を構成する目標は異なる。B の狭い置換が成功しても後者は完了しない。

## 1. 消費経路と必要な一般性

### 1.1 存在：公開入口から実際の代数まで

`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`
→ `BhattScholze.PerfectoidizationInterface.exists_perfectoidization_of_integral`
（`IntegralExistence.lean`、integral＋universal）
→ `BhattScholze.Inputs.exists_perfectoidization_of_integral`
→ `BhattScholze.exists_perfectoidization_of_finite`
→ `Inputs.exists_perfectoidization_of_finite`
→ `Perfectoidization`・`toPerfectoidization`・`isPerfectoidization_toPerfectoidization`
→ `Section2.MixedPerfectoid`・`Section2.isPerfectoidization_toMixedPerfectoid`
＝ `CLMST.RPerfd`。

| 利用箇所 | S の範囲／帰着の可否 |
| --- | --- |
| E3.integral と整代数入口 | 任意の整 R 代数、非完備も含む。有限表示・有界 p ねじれは要求しない |
| `BhattScholze.exists_perfectoidization_of_finite` | 任意の有限代数。有限表示は不要 |
| 共通 `Inputs.exists_perfectoidization_of_finite`・`Perfectoidization` | 有限かつ有限表示な任意の代数。エタール仮定なし |
| `Section2.MixedPerfectoid` | R＝`CompletedTower A t p`、S＝R⊗[A]D。A は Noether、D は有限、従って S は有限表示。定義時には domain・エタール性を要求しない |
| 主定理への適用 | A は完備正則局所環、D は有限な混標数完備局所整域。非零 g の外で D/A は有限エタール、S/R も同様。S 自体は一般に有限エタールでも R の全射商でもない |

有限代数が「何らかの perfectoid 環の商」であることも、この段階では証明されていない。
任意の多項式表示を使っても多項式環は perfectoid ではなく、根を添加した環への
S の埋め込み・全射表示・忠実な降下データを自動的には得ない。

また存在の消費は `MixedPerfectoid` の定義だけではない。実証明には次の直接呼出しがある。

- `CLMST.prop247_exists_generalRank_descent_data`（`Prop247GeneralRank.lean`）：
  André 拡大 B 上の完備テンソルの指定普遍環 P。
- `Prop247ConstantRankDescent.lean` の `B⊗[R]S`、
  `Prop247ConstantRankExcision.lean` の有限共通モデル E、
  `KLAicTorFromExcision.lean` の有限共通モデル M、
  `KLOriginalTorFromExcision.lean` の `E⊗[R]A`：いずれも整代数入口で存在を選ぶ。
- `CLMST.prop247_aic_exists_rank_comparison_data`（`Prop247RankData.lean`）：
  各 perfectoid rank 係数 Tₙ 上の有限代数 `Tₙ⊗[R]S` の普遍環。
- `CLMST.prop247_rankProductUnit_isPerfectoidization_of_finite_coefficients`：
  `∏ₙ(Tₙ⊗[R]S)` の存在を一度選び、指定直積単位の普遍性を証明する。
  ここは有限直積の普遍性の別証明で除去できる余地があるが、全存在消費は消えない。
- `BhattScholze.isIntegralPerfectoid_finPi`（`Perfectoidization/PerfectoidFiniteProduct.lean`、BR20、2026-10-25 追記）：
  有限直積の perfectoid 性。BS-W10 作業 A（cc67ea88e）で E3 に依存しない直接の証明に置き換えた（BR20、`refactor-ledger.md`）。

### 1.2 Excision：三つの適用と四辺

E3 → `BhattScholze.PerfectoidizationInterface.perfectoidization_excision_isPullback`
→ `BhattScholze.Inputs.perfectoidization_excision_isPullback`
→ `BhattScholze.klCanonicalExcisionSquare_of_excision`
（または `_of_integral_away`）→ 次の三つの適用。

| 利用箇所 | 元の射と範囲 |
| --- | --- |
| `CLMST.prop247_finiteComparison_excision` | `KLFiniteComparisonExcision R p` 全体。A,B は有限・有限表示、q:A→B は有限、核は a 冪ねじれ、余核は一様な a 冪で消える |
| `CLMST.klFiniteComparisonExcision_of_perfectoid` | 同じ型。上の支持条件から `Localization.awayMap q a` の全単射を証明し `_of_integral_away` に渡す |
| `CLMST.prop247_isogeny_of_specified` 内の hPB | A＝B⊗[R]S、X＝∏ₙ(Tₙ⊗[B]A)、q＝`prop247_rankTensorUnit`。B は AIC perfectoid、Tₙ は rank 開閉片の基底像の perfectoid 化。X が B 上有限表示であるとは仮定せず、専用の完備性・付値環延長定理を使う |

定 rank の比較は A→M←R^r（または A→E←R^r）。共通モデルは有限・有限表示で、
各比較射は指定主開集合で同型。元の A は主開集合でのみ有限エタール、
M も perfectoid／semiperfectoid 商であるとは与えられない。R^r は perfectoid。
rank 係数 Tₙ の存在は商の Cor 7.3 で賄えるが、`Tₙ⊗A` の存在はそれだけでは賄えない。

共通の四角形を記号で固定する（f:A→C、g:B→D は指定普遍単位、I＝(a)A）：

```text
C = A_perfd ──IsPerfectoidization.map hf hg q──→ D = B_perfd
│                                                    │
│ perfectoidizationClosedSideProjection hf I           │ 同 hg (IB)
↓                                                    ↓
Q = (C/IC)_perfd ─perfectoidizationClosedComparison─→ E = (D/ID)_perfd
```

Q,E は B3 の `QuotientPerfectoidization` で、元の A/I、B/IB の普遍環でもある。
底辺は `Ideal.quotientMap` が誘導する射と一致する。`KLCanonicalExcisionSquare` は
この四辺そのものの `CommRingCat.IsPullback`。`B⊗ᴸ_A A/I` を右下に使う図式ではない。
原典入力は A,B,I の導来 p 完備性と rank 1 p 完備付値環への一意延長条件。
IB の完備性や四つの辺の全射性は仮定しない。
E3 の指定 limit 錐と四普遍環の始対象性から導来四頂点も離散と分かり、
長完全列で引き戻しを得る。差 D⊕Q→E の全射性には H¹(P(A))＝0 も要る。

### 1.3 主定理までの合流

以下の矢印は「左の結果が右の証明に供給される」を表す。

- isogeny 枝：`prop247_finiteComparison_excision` と rank hPB
  → `CLMST.prop247_isogeny_of_specified` → `CLMST.proposition_2_4_7_proved`
  → `CLMST.Inputs.proposition_2_4_7`
  → `CLMST.exists_pow_annihilates_ker_coker` と `CLMST.injective_and_exists_pow_annihilates_coker`。
  後者 → `CLMST.tensor_injective_and_exists_pow_annihilates_coker`
  → `CLMST.completedTensor_injective_and_exists_pow_annihilates_coker_of_domain`
  → `CLMST.toMixedPerfectoid_injective_of_domain` および余核の零化。
  これと Koszul 比較が `completedTensor_stage_parameter_euler_comparison`
  → `CLMST.exists_selected_parameter_euler_comparison`
  → `CLMST.completedTensor_stage_parameter_length_of_source_euler_formula`
  → `CLMST.completedTower_stage_parameter_quotient_length_of_source_euler_formula`
  → `CLMST.Inputs.proposition_4_0_14` → `CLMST.parameter_quotient_length_at_stage`
  → `CLMST.parameter_quotient_length` → `Inputs.clmst_parameter_quotient_length` へ入る。
- 消滅枝：`klFiniteComparisonExcision_of_perfectoid`
  → `perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision`
  （その内部で `_of_aic_finiteComparison_excision`、二つの canonical 四角形、André 降下）
  → `CLMST.rPerfd_cohomology_vanishing_of_finiteComparison_excision`
  → `CLMST.corollary_4_0_4` → `CLMST.Inputs.corollary_4_0_4`
  → `CLMST.parameter_koszul_annihilates_of_etale`
  → `CLMST.exists_perfectoidIdeal_annihilates_koszul`
  → `Inputs.clmst_exists_perfectoidIdeal_annihilates_koszul`。
  この消滅は上のパラメータ Euler 比較にも使われる。
- 両枝＋`Inputs.clmst_length_eq_zero_of_perfectoidIdeal_annihilates`
  → `Section2.mixedPerfectoid_length_properties`
  → `Section2.lengthAlgebra_mixedCharacteristic` → `Section2.theorem_2_5`
  → `Section5.core_of_normalization_bases`（二つの正規化基底で適用）。
  その内部の長さ代数の経路は `core_of_lengthAlgebras_with_parameter_choice`
  → `core_of_lengthAlgebras`（`twistedEuler_pos_of_lengthAlgebras`、
  `lambdaChi_pos_of_parameter_lengthAlgebras`、`lambdaChi_pos_of_parameter_tower` を使用）。
  → `Section5.core_of_complete_algClosed` → `core_statement`。
  任意加群・剰余体・完備化の帰着は順に `Section5.positivity_of_complete_algClosed`
  → `positivity_of_complete_residueCharP` → `positivity_of_residueCharP` → `main_statement`。
  剰余標数零の枝に BS は不要。

## 2. B：既証部品だけの別証明の可否

| 消費／試み | 判定と理由 |
| --- | --- |
| (g)_perfd、閉側 Q,E、rank 基底像の商 | 可。Cor 7.3 の存在＋Thm 7.4 の全射性、普遍性による単位の同定で足りる。既に実装されている |
| 既に与えた S_perfd の André 底変換 | 可。Prop 8.13 環版と Lemma 10.3、通常／導来完備化比較で同じ単位の普遍性を移す。既実装 |
| S＝R⊗[A]D、有限共通モデルの存在 | 不足。André は R→B を忠実にするが B⊗S を B の商にはしない。有限エタール性は D(g) 上だけ。開側での分解から閉側を含む普遍 perfectoid 環を貼る定理がない |
| Prop 8.13 で存在を逆算 | 不可。同定理の環版は指定済みの perfectoid 化を入力にする。存在を同じ入力から取り出すのは循環 |
| Lemma 10.3 で excision を得る | 不足。perfectoid 環間の完備テンソル（余積）の離散性は、有限比較・rank 図式の引き戻し保存を与えない |
| Thm 7.4 の全射性と環の普遍性で四角形を貼る | 不足。普遍性で調べられるのは perfectoid 標的への射。環の引き戻しは任意の環からの射を検出し、二者は同値ではない。候補 pullback の perfectoid 性・正確性も未証明 |

CLMST Prop 2.4.7 の数学的な手順は、André 底変換→AIC 上で D(g) の有限被覆ごとに分解
→S_perfd と R^r の almost 比較→Claim 2.4.8 の核・余核評価→錐の零射の降下。
**「almost 比較」の供給が BS Cor 8.12／Thm 10.9 の箇所**であり、Claim 2.4.8 は
そこを証明しない。Cor 4.0.4 でも Prop 2.4.9(a) の全 p 冪ねじれ Tor 入力が必要で、
g を逆にして平坦という事実だけでは元の (g)_perfd の全元による零化は得られない。
原典の Σ_r-Galois 閉包を省いて実装の有限共通モデルで進んでも、二つの excision は残る。

従って B を続けるなら新たに必要なのは、(i) 有限エタール away の普遍環の構成と忠実降下、
(ii) 上記の有限比較と一般 rank の四角形に対する正確な貼り合わせ。
これらを証明できれば後段は再利用できるが、現在は証明の閉じた案ではない。
調査 1–2 人週、成立する構成を得た後でも特殊化した降下・貼り合わせに概算 12–30 人週以上。
未解決の構成をこの数字で完成保証しない。全 E3 を得るにはさらに任意通常代数への拡張が必要。

## 3. A：原典の対象を構成して各欄を満たす

### 3.1 依存順の最小実装単位

全論文を移植する必要はない。固定した完全 prism (A,(d)) 上の affine な比較から始める。
以下は原典の証明の必要部分を切り出した DAG。後段を前段の入力へ逆流させない。

| 順序 | 原典の必要部分／供給するもの | 既存と不足、追加工数 |
| --- | --- | --- |
| A0 | §4.1・Rem 4.6・Lemma 4.8、Construction 4.17–18、Lemma 4.20–21：prismatic site、完全試験 prism、Čech 計算と自然性 | prism/perfectoid 対応は既存。Lemma 4.8 は有界な向き付き prism を標的とする形で証明済み（`Andre/Remark715/PerfectPrismBoundedTargetLift`、主経路外。2026-10-25 の第 3 章の精読で判明、BR33 で Prism/ へ移す）。site／係数付き導来切断は未実装。4–8 人週 |
| A1 | Thm 5.2、Lemma 5.4、Cor 5.5 → Construction 6.1・Prop 6.2 → Thm 6.3＝Thm 4.11、必要な Cor 4.12・de Rham 比較 | PD 計算・複体基盤は既存。affine 空間の結晶比較、Cartier、HT 比較の射と乗法・Frobenius 整合は不足。8–18 人週 |
| A2 | Construction 7.6：smooth／多項式上の Δ を左 Kan 延長、HT filtration・base change・余極限保存 | P_Σ の一般論を再利用。animated 代数の具体的表示、cotangent complex・導来外冪、完備化と E∞ 構造付き Δ の接続が不足。6–14 人週 |
| A3 | Lemma 7.7、Example 7.9・Prop 7.10 の必要部分：離散時 δ 構造と semiperfectoid 計算 | Cor 7.3・Thm 7.4・André の証明は再利用。既存の普遍環と Δ の比較は別証明。3–7 人週 |
| A4 | Def 8.2、Lemma 8.4：Frobenius 余極限の (p,d) 完備化と mod d | perfd・unit・h0・coconnective。P⁰ と levelwise Frobenius の比較、p 完備 E∞ 演算と torsion 論が不足。3–7 人週 |
| A5 | Lemma 8.6 → Prop 8.5：根添加の descendability、semiperfectoid Čech 計算と完全標的の極限 | limitCone・limit_isLimit。指定単位、H⁰ の乗法、Type u 標的への制限の比較まで必要。4–9 人週 |
| A6 | Def 8.7・Lemma 8.8 → Prop 8.10（affine 部分）→ Cor 8.11 → Cor 8.12 | arc／valuation、tilt・Witt・完備化による descent、sheaf pushout が不足。既存 U の極限保存で D(R) の excision へ。5–12 人週 |
| A7 | Prop 8.13 の導来版 → Cor 8.14 | universal。環版では代用できない Δ の対称モノイダル性と離散時 perfectoid 性を証明。A2–5 後 1–3 人週 |
| A8 | Lemma 10.3・Prop 10.4 の必要部分 → Lemma 10.5、Thm 10.9 の almost-connective 部分、Lemma 10.12 → Thm 10.11 | integral。Lemma 10.3 と almost 加群論は既存。非有界複体の必要な切断、層別・近似、rank 分解と arc 比較が不足。4–10 人週 |
| A9 | 非完備 S の H⁰ 導来完備化、指定錐の輸送、E3 の束への代入 | 環 Hom の一意延長・Π2 の橋は既存。Δ の比較を単位・全射に自然な形で接続。1–3 人週 |

合計の単純和は 39–91 人週。共通部分の重複を除いても **約35–85人週**を計画幅とする。
A0–3 が最大の不確実性。§9 の étale 比較、§11 以降、一般 formal scheme への大域化、
André の mod p ind-syntomic 強化、Thm 10.9 の almost finite projective 全体は E3 に不要。
原典 Prop 7.2 の全 prism の始対象も、A3 で既存の完全標的の初期性と直接比較できれば省ける。

### 3.2 外部文献の必要な切片（新しい引用入力の提案ではない）

| 順序／文献 | 原典で使う最小範囲と切り落とせる部分 |
| --- | --- |
| A5：[Mat16] | descendable の定義、fiber の有限テンソル冪零による判定、Čech totalization の復元。Galois 群の理論全体は不要 |
| A5–6：[BS17] | Lemma 11.22（Frobenius 余極限後の descendability の一様指数）、Thm 4.1（perfect affine の O の v-descent）、Lemma 6.3（valuation の切断貼合せ）。Lemma 3.16 は既存の完全環 Tor 消滅で代替済み |
| A4：[Lur11] | Remark 2.2.7 の P⁰ が正の homotopy を殺す事実と、単体的余単体的 F_p 代数の Frobenius が P⁰ を誘導する比較。一般 p-adic homotopy 理論は不要 |
| A6：[BM18] | Def 1.2 と Thm 1.6 のうち、v-descent＋valuation excision から arc-descent を得る向き。BS 脚注13は v 版だけなら回避可能と言うが、E3 の現行 ArcOutside 全体にはそのまま使えない |
| 原典 §10 の全面移植時：[And18b] | Prop 1.9.1（almost G-Galois から almost 有限射影・非分岐）、Lemma 1.9.2（有限エタールの対称群閉包）。AIC 局所分解＋共通有限モデルで almost-connectivity だけを証明する A8 では省ける |
| 同：[GR03] | §2.1.1 の basic setup、必要なら §2.5.15 の平坦性条件と almost 加群計算。有限射影性全体を目標から外し既存 almost API を使う A8 では新規依存を省ける |

したがって六文献のうち、採用する証明切片で外部数学を新たに実装する最小採用集合は
**{BS17, BM18, Mat16, Lur11}**。絶対的な不可欠性・最小性の定理という意味ではない。
Thm 10.9 を原典の Galois→almost 有限射影の経路まで逐語的に移すなら六文献全部となる。
四文献へ減らす A8 の証明概略は、André 後に各定 rank 片を主開被覆上で R^r と比較し、
二つの導来 excision から P(S) が各元について almost 離散と示し、rank 四角形で合流するもの。
この段階では **A6 の excision は証明済みとして使う**ので B の循環とは異なる。
Lemma 10.5 と層別帰納で離散性を得るには full almost purity の有限射影性は使わない。

六文献以外の隠れた負債もある。原典経路の A1 は Berthelot [Ber06] の結晶計算と Cartier、
A2–3 は cotangent/quasisyntomic 論（[BMS19, §4.4・Rem 4.22]）と非可換導来関手の
HTT §5.5.9／§5.5.8 型の一般論を使う。これらを四文献に含めたことにはしない。
既存 PD 計算から比較を直接構成できる範囲は縮約し、残りは証明対象として A1–3 に計上する。

### 3.3 基盤との境界と最初の受渡し条件

- EInfinity：`BarrattEccles.CAlg_R`、`cAlgForgetDerived`、
  `cAlgForgetDerived_mapJoinCone_isLimit`、離散環・H⁰・元の単位の比較を再利用。
  これは Δ、Frobenius、P⁰、animated 可換環と E∞ 代数の比較を供給しない。
  特に正標数で可換 dg 代数を全 E∞ 代数と同一視しない。
- F2/Presentable：最新の `infinity-core-presentable.md` が優先。
  P_Σ の sifted／filtered・幾何学的実現による普遍性、presentable の小極限は提供済み。
  旧 E2 計画の N 節にある「P-1 g 未完了」は古い。一般随伴関手定理・局所化存在は残るが、
  BS に要る具体的左 Kan 延長までそれらに一括依存させない。多項式代数を選ぶ具体化は BS 側。
- Derived：`derivedInfinityCategory`、安定性、Hⁱ・離散性、指定四辺の三角・長完全列、
  完備テンソル・スカラー制限は再利用。構造層の導来切断や prismatic filtration は別。
- DifferentialGraded：解像・dg nerve・導来 Hom 等のモデルを利用できる。
  一般的な dg／K 理論の完成を prismatic／arc／結晶コホモロジーの完成とは数えない。
- 最初の実装単位は固定完全 prism 上の多項式一変数の Čech モデルと HT 比較。
  その単位・乗法・Frobenius・mod (p,d) が一致してから多変数・左 Kan 延長へ進む。
  A5 では u-small cover の指定 totalization を構成し、単なる巨大極限の制限で済ませない。
  A9 では元の非完備 S の unit と Hom 不変性を保持し、S 自身の完備性を追加しない。

## 4. A・B・C の選択と停止条件

| 案 | 到達点・負担 | 推奨 |
| --- | --- | --- |
| A：上記を証明 | E3 の全欄を元の範囲・単位・指定錐で構成し、現存の一入力そのものを除去。約35–85人週 | 厳密な引用除去の本線。A0–1 を小さく区切って見積りを更新 |
| B：CLMST 特殊形を迂回 | 現状は存在と貼り合わせが未解決。成功しても主定理の依存を外すだけでは全 E3 の証明にならない | 短い追加調査に限定。既証五部品だけで完成するとして実装を始めない |
| C：外部引用を受容 | 現在の E3 一入力を維持するなら実装追加なし。原典切片へ分割して引用しても未証明依存の場所が変わる。仕様・対応の整理は1–2人週程度 | 引用を許す成果物には合理的。今回の「入力を消す・新規引用なし」の完了条件は満たさない |

推奨は A。ただし最初に固定 affine の A0–1 の設計を固め、その実績で全体幅を更新する。
B を採る判断は、有限比較と rank 四角形の正確な貼り合わせの独立証明、および有限代数の
普遍環の構成が紙上で閉じた時に限る。C はユーザーが引用受容へ目標を変更した場合の選択肢。
この BS-0 はここで停止し、他レーンの実装・主計画・解説・Inputs は変更しない。

確認範囲：本文の利用経路と基盤の到達点はソースおよび計画文書の読み取りに基づく。
既存 root olean を import する一時ファイルで `lake env lean` の `#print axioms`・`#check`
だけを試みたが、結果出力前に長時間待ちとなり中断した。新たな公理監査の成功は主張しない。
ビルド・olean 再生成は実行していない。
