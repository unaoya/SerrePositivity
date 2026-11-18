# BS-W12 停止点 0（2026-11-07）

`math/bs-impl` を `main` の `9e42e3321` へ fast-forward し、W12 §2 と原典を照合した。経路 B の二つの置き換えは、構造層の完全標数 $p$ の場合に必要な形で成り立つ。以下は紙での確認と Lean の型案。

## B1 の配置と⑥との照合

`main` の `AlgebraicGeometry/` を `cech`・`čech`・`amitsur` と忠実平坦降下で検索し、⑥の `math/scheme`（`ed493953e`）の差分と作業木も確認した。増大 Amitsur 複体の完全性、切断、または二重 Čech 複体による消去に当たる実装は見つからなかった。既存の忠実平坦降下は Mittag–Leffler 性や射影性に関するもの。⑥の 2g の報告には第一象限の二重複体の設計がある。[⑥の停止点 2a 報告 §5](../../stage-ii/scheme/scheme-w1-2a-report.md#5-段-2g2h--全次数の判定と-affine-への出口)

B1 の新規ファイルは `SerrePositivity/HomologicalAlgebra/Cech/` に置く案で進められる。`HomologicalAlgebra/Cosimplicial/SplitCechConerve` に `cechAugmentation_retraction`・`cechSplitHomotopy`・`cechSplitCochainEquiv` があるので、切断の収縮に再利用する。`KST/Descent/DoubleCechDescent` は空間値の極限比較。共有側は第一象限の複体の比較を切り出し、⑥の前層複体と⑤a の affine 環の両方から使える形にする。⑤b の差分・作業木にも対象パスの重複はない。

## §2.1　Lemma 4.5 の代わりに有限段で切断を作る

$V$ を標数 $p$ の絶対整閉付値環、$V\to B$ を完全代数の一射の arc 被覆とする。$B$ を有限表示 $V$ 代数 $C_i$ の filtered colimit として書き、完全化が filtered colimit を保つので $B=\operatorname{colim}_i C_i^{\mathrm{perf}}$ とする。各 $V\to C_i^{\mathrm{perf}}$ は元の被覆 $V\to B$ で細分されるので arc 被覆。`C_i^{perf}` 自体への有限表示性は仮定しない。[BM18 Proposition 4.8、証明冒頭](https://arxiv.org/pdf/1807.04725#page=28)

素点 $\mathfrak q$ での試験には階数 0 の $k=\kappa(\mathfrak q)$ を使う。$V\to k$ に対する arc の持ち上げは $C_i^{\mathrm{perf}}\otimes_V k$ から非零環への射を与える。そのため $C_i\otimes_V k\ne 0$。$V/\mathfrak q$ は絶対整閉整域で、その分数体 $k$ は代数閉体。有限型 $k$ 代数 $C_i\otimes_V k$ の極大イデアルを選ぶと、弱 Nullstellensatz により剰余体が $k$ となり $V$ 上の射 $C_i\to k$ が得られる。[BM18 Definition 3.26](https://arxiv.org/pdf/1807.04725#page=22)・[Stacks 10.34.1](https://stacks.math.columbia.edu/tag/00FV)

$V_{[\mathfrak p,\mathfrak q]}=(V/\mathfrak p)_{\mathfrak q}$ と書く。直後の素点がなければ $k$ は $\mathfrak q'\supsetneq\mathfrak q$ を下げた $V_{[\mathfrak q,\mathfrak q']}$ の余極限。直前の素点がない場合も $\mathfrak q'\subsetneq\mathfrak q$ を上げた $V_{[\mathfrak q',\mathfrak q]}$ の余極限になる。前者では局所化で反転する元の合併、後者では下側の素イデアルの合併を使う。有限個の生成元の像と有限個の関係式が有限段でそろうため、$C_i\to k$ は対応する非退化な区間の $V_I$ に降りる。$V_I$ は標数 $p$ の絶対整閉付値環なので完全であり、射は $C_i^{\mathrm{perf}}\to V_I$ へ延びる。したがって $V_I\to C_i^{\mathrm{perf}}\otimes_V V_I$ は環として左逆を持ち、底変換後も増大 Čech 複体が収縮する。隣接素点がある場合はその階数 1 の区間を使える。階数 0・1 の区間では arc の持ち上げが忠実平坦な拡大 $V_I\to W$ 上の切断を与え、B1 の忠実平坦反映で普遍完全性が従う。ここまで ⑥の v 降下は不要。これで Proposition 4.8 の (3)・(4) に必要な結論が得られる。[BM18 Lemma 4.5、Definition 4.6、Proposition 4.8](https://arxiv.org/pdf/1807.04725#page=27)

## §2.2　Milnor 短完全列と区間の貼り合わせ

$V$ を完全な標数 $p$ の付値環とする。絶対整閉な標数 $p$ の場合は、$X^p-a$ の根の存在と整域での単射性からこの仮定を得る。Frobenius とその逆は素イデアルを保つので、$V/\mathfrak q,V_{\mathfrak q},\kappa(\mathfrak q)$ は完全。任意の完全 $V$ 代数 $D$ に対し、既存の `valuationRing_milnorSquare` を $V$ 加群の短完全列と読み替える。$\operatorname{Tor}_1^V(D,\kappa(\mathfrak q))=0$ と Tor の長完全列から、$D\otimes_V-$ を施した列も短完全になる。有限直積は加群として直和で、最後の射は剰余二射の差。従って底変換後も環の引き戻し。ここで必要な Tor は `tor_vanishing_of_perfect`、零環を含める入口は `perfectRing_tor_subsingleton_of_char_eq_zero`。長完全列は `TorLES` に既存の入口がある。[BM18 Lemma 4.4](https://arxiv.org/pdf/1807.04725#page=26)・[BS17 Lemma 6.3](https://arxiv.org/pdf/1507.06490)

重なる区間の和を基底に取れば、$I=[0,\mathfrak p]$、$J=[\mathfrak q,\mathfrak m]$、$\mathfrak q\subseteq\mathfrak p$ に帰着する。$J'=[\mathfrak p,\mathfrak m]$ と取ると、全区間は $I\cup J'$、$J$ は $(I\cap J)\cup J'$ であり、いずれも交わりは $\{\mathfrak p\}$。まず $V$ に、次に $V_J$ に上の短完全列を使う。後者の係数 $D\otimes_V V_J$ も完全。二つの引き戻しを貼り合わせると、任意の完全 $V$ 代数 $D$ について $D\simeq(D\otimes_V V_I)\times_{D\otimes_V V_{I\cap J}}(D\otimes_V V_J)$ を得る。さらに $V_I\to V_{I\cap J}$ は $V_{\mathfrak p}\to(V/\mathfrak q)_{\mathfrak p}$ という全射なので、剰余の差の射も全射。これが Proposition 4.8 の (6)・(7) を短完全列にした形。[BM18 Proposition 4.8 (5)、図式 (6)・(7)](https://arxiv.org/pdf/1807.04725#page=29)

普遍完全性の判定では、任意の完全 $V$ 代数 $T$ と $T\to B\otimes_V T$ の増大 Čech 複体の各項 $D$ にこの列を適用する。増大項は $T$、残りは完全環の通常の有限テンソル冪であり、`perfectCoefficientTensor_perfectRing` が完全性の入口。射・テンソルの比較は自然なので交代余面と可換し、増大を含む複体の短完全列になる。三つの区間での完全性からホモロジー長完全列で元の複体の全次数の完全性が出る。$I,J$ 上の普遍完全性から交わり上の完全性も出る。Lemma 4.3 の付値環間の素点の記述と Proposition 3.32 による検出はこの手順に要らない。内部 API では $p\cdot 1=0$ と `PerfectRing` で零環を含め、既存の `CharP` 入力には非零の場合だけ接続する。

## 型案と規模

$E(f)$ を、環準同型 $f:A\to B$ の `Arrow.augmentedCechConerve` に対する `AugmentedRingCechExact` と書く。増大の単射性、次数 0、全正次数を保持する。$E_p^{\mathrm{univ}}(f)$ は任意の完全標数 $p$ の $A$ 代数 $T$ に対する $E(T\to T\otimes_A B)$。共有部分は完全性や標数を仮定しない形で考える。以下の行数は増分の概算で、Lean の実測ではない。

| 部品 | 主張の型案 | 見込み |
| --- | --- | --- |
| B1 | `AugmentedRingCechExact` と一射への包装。平坦な $A\to T$ で $E(f)\Rightarrow E(f_T)$、忠実平坦で同値。環の左逆があればすべての底変換で $E$。二射 $A\to B,A\to C$ が互いの正のテンソル冪への底変換ですべて $E$ なら、第一象限の二重複体を介して $E(A\to B)\Leftrightarrow E(A\to C)$。合成 $A\to B\to C$ の場合は $C$ のテンソル冪上で $A\to B$ の底変換に切断があるので、$E(A\to C)$ とその $B$ の正のテンソル冪上での $E$ から $E(A\to B)$。任意の許された基底への底変換を量化すれば普遍版。環の射の filtered colimit では各段の $E$ から極限の $E$。 | 1,000–1,900 行。余面・テンソル比較と行／列から Tot への擬同型が主な不確実性。 |
| B2 | $V,\mathfrak q,D$ に対する $V$ 加群の Milnor 短完全列のテンソル版。$I,J,I\cap J$ での $E$ から $E$ を検出し、$E_p^{\mathrm{univ}}$ の貼り合わせへ渡す。 | 350–650 行。Tor の次数 0 の比較と区間の射の整合。 |
| B3 | 素点の組 $\mathfrak p\subseteq\mathfrak q$ から $V_I$ を作り、区間包含を反変の射へ移す。絶対整閉性・完全性、端点の余極限と有限表示模型の切断の降下、Lemma 4.7 の 5 条件から全区間への Zorn。 | 700–1,200 行。絶対整閉性の商・局所化・剰余体は既存。端点の両方向の図式と Zorn が主。 |
| B4 | 各係数環が絶対整閉付値整域なら、ultrafilter による超積も同じ。$R=\prod W_t$ 上では、各 ultrafilter 局所化 $R_{\mathcal U}$ への底変換後の $E$ から $E$ を検出する。 | 450–900 行。超積を指示冪等元 $e_J$（$J\in\mathcal U$）の局所化と同一視する。任意の素イデアル $P\subset R$ は $e_J\notin P$ で ultrafilter を与え、$R_P$ はその局所化を経由する。平坦局所化とホモロジーの消滅判定を使う。 |
| B5 | 完全 $A$（型は `Type u`）に対し、`Type u` の添字 $t$、絶対整閉付値整域 $W_t$、射 $A\to W_t$ を取り、一射 $A\to\prod_t W_t$ が affine の v 被覆。 | 400–850 行。付値を代数閉包へ延長する。大きい絶対整閉付値環 $W$ に対し、像の分数体の相対代数閉包 $K_1\subset\operatorname{Frac}(W)$ と $W\cap K_1$ を使う。濃度は $\max(\#A,\aleph_0)$ 以下。固定した濃度の台の部分集合と環構造・射を `Type u` で符号化する。 |
| B6 | 下書きの `cech_exact_of_arcCover_perfect` の型。完全な有限族を積への一射にし、完全な基底への底変換と有限表示模型、B2–B5 を適用する。B5 の積を $R$ として、⑥の `cech_exact_of_vCover_perfect` を $A\to R$ と $B$ の正のテンソル冪への底変換で使う。B4 と区間の議論から $R\to B\otimes_A R$ は普遍完全なので、$R$ の正のテンソル冪への底変換でも完全。B1 の二射の比較で $E(A\to B)$ を得る。 | 450–850 行。⑥の BS17 Thm 4.1 (i) 待ち。 |

B1 の合成からの消去には、合成自身の完全性と、二重複体の行に必要な底変換後の完全性の両方を入力とする。平坦性を仮定しない場合は、必要な底変換後の完全性を個別に供給する。B6 では v 被覆が底変換で保たれることと、完全標数 $p$ では通常のテンソルが完全であることを用いる。原典の役割分担は BS 著者版 Proposition 8.10 の証明、BM18 Lemma 3.4・3.25・3.27・3.29・Proposition 3.30、BS17 Thm 4.1 (i) に対応。[BS 著者版](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=67)・[BM18](https://arxiv.org/pdf/1807.04725)・[BS17](https://arxiv.org/pdf/1507.06490)

合計は約 3,350–6,350 行。実装順は W12 の B1、B2・B3、B4・B5、B6 の型の確認。段 0 はこの報告のみ。Lean の編集・型検査・ビルド・監査は実施していない。段 1 の開始は調整役の確認を待つ。

## 停止点 1（B1、2026-11-07）

`main` の `30d46f897` を `math/bs-impl` に取り込み（`9adc341c8`）、指示書 §5 を読んで実装した。⑤b と⑥の作業木および枝の差分を再確認し、新規 Čech モジュールと報告の編集先に重複はなかった。

`SerrePositivity.Cech.AugmentedRingCechExact` は `drafts/A6/ArcSheafProperty.lean` の定義と定義的に同じで、増大射の単射性、通常の次数 0、全正次数の完全性を表す。`ringCechExact_iff_acyclic` は増大項を次数 0 に置いた複体の全次数の完全性との同値。環の射には `IsCechExact (Arrow.mk f)` を使う。

- `isCechExact_baseChange` は平坦底変換で保存し、`isCechExact_baseChange_iff` は忠実平坦底変換で反映する。各項の有限余積を基底環の下の圏で比較してから、加群のテンソル積に移す。
- `isCechExact_of_retraction` は環として左逆がある場合。既存の `cechSplitHomotopy` と `cechAugmentation_retraction` を再利用した。`isCechExact_baseChange_of_map` は底変換先への代数準同型から左逆を作る。
- `isCechExact_iff_of_tensorCech` は二射の正次数の Čech 項上で互いの底変換が完全なとき、元の二射の完全性を比較する。`isCechExact_of_comp` では合成 $A\to C$ 自身とその $B$ の正次数の各項上での完全性を仮定し、$C$ の各項上での $A\to B$ は切断により完全と示した。[BM18 Lemma 3.4](https://arxiv.org/pdf/1807.04725)
- `isCechExact_colimit` は環の射の filtered 図式に対する保存。`ringCechExact_colimit` は増大余単体対象の filtered 図式版で、図式の `HasColimit` を受け取る。
- ⑥の入口は `doubleCech_acyclic_iff`。二つの増大単体圏の積から加法群への図式を受け取る。`exact_zero_row_iff_zero_col_of_commute` は可換な微分を持つ第一象限の増大二重複体に直接使える。全複体のサイクルを次数ごとの有限な対角線で消去して、零番の行と列を比較した。

取り込み時に入口・監査への登録を依頼するモジュールは次の 7 本（1,364 行）。

- `SerrePositivity.HomologicalAlgebra.Cech.Basic`
- `SerrePositivity.HomologicalAlgebra.Cech.BaseChange`
- `SerrePositivity.HomologicalAlgebra.Cech.Split`
- `SerrePositivity.HomologicalAlgebra.Cech.Filtered`
- `SerrePositivity.HomologicalAlgebra.Cech.Diagonal`
- `SerrePositivity.HomologicalAlgebra.Cech.Double`
- `SerrePositivity.HomologicalAlgebra.Cech.Composition`

専用 worktree で共有ロック付きの対象ビルドが成功した（7 本、依存を含む Lake の集計 2,130 jobs、最終回 16 秒、対象の Lean 警告なし）。新規 7 本の `import all` による監査は 207 宣言が標準三公理のみ。新規宣言の `sorry`・`admit`・追加公理は 0。import 閉包に E3 の `PerfectoidizationInterface` はなく、既存の Lean 宣言に差分なし。`git diff --cached --check` も通過した。停止点 1 で調整役による取り込みを待つ。

## 停止点 2（B2・B3、2026-11-07）

`math/bs-impl` を `2553b6e93` へ fast-forward してから開始した。⑤b・⑥の作業木と枝の差分を確認し、編集先に重複はなかった。

### B2　完全代数とのテンソルと Čech 完全性の検出

- `milnorModuleComplex_shortExact` は BS-W11 の `valuationRing_milnorSquare` の加群版。`milnorModuleComplex_tensor_shortExact` は完全代数とのテンソル後の短完全性を、`PerfectTorIndependence.Basic` が再利用する `perfectRing_tor_subsingleton_of_char_eq_zero` と Tor の長完全列から示す。係数の零環を含む。
- `cechConerve_perfectRing` は広い押し出しに各脚の逆 Frobenius を延ばし、増大 Čech 複体の各項で使う完全性を与える。`moduleCech_tor_subsingleton` は完全な係数環に対する各項の Tor 消滅。
- `cechExact_of_milnorTensor` は局所化、商、剰余体の三つで検出する。`cechExact_of_overlapTensor` は重なる二つの区間と交わりの三つで検出する。後者は、停止点 0 の二つの四角形を貼る計算を、局所化から交わりの区間環への全射とその核の直接計算に置き換えた。得られた短完全列に各次数の Tor 消滅を使い、複体の短完全列から完全性を得る。[BM18 Lemma 4.4・Proposition 4.8 の証明 (5)、図式 (6)](https://arxiv.org/pdf/1807.04725#page=29)

### B3　付値環の区間、剰余体への近似、Zorn

- `ValuationIntervalRing` は下端で割って上端で局所化した環。`intervalRingMap` は区間の包含と逆向きで、`valuationRing_interval` はその環が付値環であることを示す。既存の絶対整閉性の商・局所化の補題を再利用して `aic_interval` と `IsAbsolutelyIntegrallyClosed.primeResidue_isAlgClosed` を得た。`IsAbsolutelyIntegrallyClosed.perfectRing_of_charP` は標数 p の絶対整閉整域の完全性。
- `intervalRingCoconeIsColimit` は縮小する有向区間族の共通部分の環を余極限として表す。`intervalAboveColimitIsoResidue`・`intervalBelowColimitIsoResidue` は直後・直前の素点がないときの剰余体版。`exists_intervalRingFactor_of_finitePresentation` は有限表示の代数から剰余体への射を区間の有限段へ降ろす。
- `valuationIntervalProperty_of_localExtensions` は左端を固定し、良い右端に Zorn を適用する。Lemma 4.7 の長さ ≤ 1 の条件からは一点区間だけを使用する。部分区間への制限、左右への延長、重なる区間の貼り合わせはそれぞれ仮定にした。[BM18 Definition 4.6・Lemma 4.7・Proposition 4.8](https://arxiv.org/pdf/1807.04725#page=27)

取り込み時に入口・監査への登録を依頼するモジュールは次の 11 本（1,275 行）。

- `SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic`
- `SerrePositivity.CommutativeAlgebra.ValuationInterval.Colimit`
- `SerrePositivity.CommutativeAlgebra.ValuationInterval.FinitePresentation`
- `SerrePositivity.CommutativeAlgebra.ValuationInterval.Endpoint`
- `SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorTensor`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorDetection`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectCech`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechMilnor`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcIntervalOverlap`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechOverlap`

共有ロック付きの対象ビルド成功（11 本、Lake の依存込み集計 3,497 jobs、17 秒）。新規モジュールの Lean 警告は 0。既存の `ArcValuationMilnor.lean` では `valuationRing_milnorSquare_perfect` の未使用の節引数の警告が再掲された。新規モジュールを `import all` で監査し、133 宣言が標準三公理のみ。新規の `sorry`・`admit`・追加公理は 0。E3 は import 閉包に含まれず、既存の Lean 宣言に差分なし。`git diff --cached --check` を通過。段 3 は §3 の事前承認の条件に従って開始する。

## 停止点 3（B4・B5、2026-11-07）

⑤b・⑥の作業木と枝の差分を再確認し、新規の編集先に重複はなかった。

### B4　超積と完全性の検出

- `RingUltraproduct` は超フィルター上で零になる元で割った商。`valuationRing_ultraproduct` は整除の二択を超フィルターで選ぶ。`aic_ultraproduct` は各成分でモニック多項式の根を選び、直積から商へ移す。完全標数 p の入口は `perfectRing_ultraproduct_of_aic`。[BM18 Lemma 3.27](https://arxiv.org/pdf/1807.04725#page=22)
- `isLocalization_ringUltraproduct` は超フィルターの指示冪等元による局所化。`ultrafilterOfPrime` は積環の素点の外にある指示冪等元から超フィルターを作る。`subsingleton_of_ultraproduct_tensor` は加群の元の零化イデアルを含む素点で零性を検出し、`cechExact_of_ultraproducts` は平坦局所化とホモロジーの可換性を使って増大 Čech 複体に適用する。[BM18 Lemma 3.25](https://arxiv.org/pdf/1807.04725#page=22)

### B5　代表付値環の積による v 被覆

- `exists_valuationSubring_algebraicClosure` は分数体の代数閉包へ付値環を忠実平坦に拡大する。`exists_valuationProbe_factor` は絶対整閉な試験付値環への射を小さい代表で因子化し、代表から試験付値環への射も忠実平坦と示す。[BM18 Lemmas 3.28・3.29](https://arxiv.org/pdf/1807.04725#page=23)
- 代表の添字は、素点ごとの固定した `AlgebraicClosure (FractionRing (A ⧸ P))` のうち基底環の像を含む付値部分環。環構造を集合上に符号化する方式の代わりに、この添字で `Type u` に収めた。各代表の濃度は `valuationProbe_cardinal_le` で `max (#A) ℵ₀` 以下。
- `valuationProbeProduct_vCover` は代表の積への射が `IsAffineVCover` であることを示す。`valuationProbeProduct_perfectRing` は `(p : A) = 0` から積の完全性を得る。空の積もこの形で扱える。[BM18 Proposition 3.30](https://arxiv.org/pdf/1807.04725#page=23)

取り込み時に入口・監査への登録を依頼するモジュールは次の 5 本（573 行）。

- `SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic`
- `SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization`
- `SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechUltraproduct`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationProduct`

共有ロック付きの対象ビルド成功（5 本、Lake の依存込み集計 3,499 jobs、17 秒）。新規モジュールの Lean 警告は 0。既存の `AbsolutelyIntegrallyClosed/Basic.lean` と `ArcValuationMilnor.lean` の警告が再掲された。新規モジュールの `import all` による監査は 61 宣言が標準三公理のみ。新規の `sorry`・`admit`・追加公理は 0。E3 は import 閉包に含まれず、既存 Lean 宣言の変更はない。`git diff --cached --check` を通過した。

## 停止点 4（B6 の型、2026-11-07）

[drafts/A6/ArcRouteB.lean](../drafts/A6/ArcRouteB.lean) に G-A6-1 の結論 `ArcRouteBGoal` と ⑥ の入力 `BS17VCechInput` を置いた。元の [ArcSheafProperty.lean](../drafts/A6/ArcSheafProperty.lean) から被覆・余脈体・完全性の定義と二つの定理の型を取り出し、両方について `Iff.rfl` で一致を検査した。⑥の本体が取り込まれる前なので、接続の型検査では BS17 を明示的な仮定として受け取った。

- `cechExact_of_affineVCover_from_BS17` は一射を一要素の有限族にし、積と元の環の同型に沿って完全性を移す。完全標数 p の入口 `cechExact_of_perfectAffineVCover_from_BS17` は、零基底では切断、非零基底では剰余体での v 被覆の試験により型を揃える。
- `isAffineVCover_tensor` と `cechExact_valuationProbeProduct_tensor_from_BS17` で、B5 の積射を完全係数に底変換して ⑥ に渡せる。通常のテンソル積の完全性は零環も含めた。
- `cechExact_of_valuationProbeTests` は ⑥ の入力から積射自身と、B の正次数の各 Čech 項上での積射の完全性を得て、B1 の比較に渡す。残る仮定は、積射の正次数の各項上での B の底変換の完全性。ここは B4 で超積へ帰着し、B2・B3 と有限表示模型、階数 ≤ 1 の切断から閉じる。有限族の積への縮約も、最終の `ArcRouteBGoal` の証明に残る。[BM18 Proposition 4.8](https://arxiv.org/pdf/1807.04725#page=28)・[BS 著者版 Proposition 8.10](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=67)

drafts の新規ファイルと型比較の両方が、共有ロック付きの `lake env lean` で警告なしに通った。新規の本体モジュールや登録対象はない。G-A6-1 の証明を本体へ移すのは、⑥の BS17 Theorem 4.1 (i) の取り込み後とする。
