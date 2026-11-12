# BS 勉強ノートの赤い囲み（リファクタ候補）の原文

`exposition/ja/bs/*.html` の `<div class="box refactor">` の中身を ba24dceb6 時点で写したもの（HTML の印を Markdown に直しただけで、文は変えていない）。見出しの「ファイル:行」は囲みの開始行。一覧と現状は `README.md`。

### 00-map.html:135

BR1　直下 618 ファイルの平置き

（W1 前の記録）主題（δ 環の一般論、prism、根付き拡大、perfectoid 化の普遍性）で分かれていなかった。W1（主題別）・W2（原典の節ごと）・W3・W4 で上の表の形にした。`Delta/`、`Prism/`、`RootedExtension/`、`Perfectoidization/` のようなサブディレクトリに分ける案がある。外から import されるモジュール（`EInfinity/Perfectoidization/`、`CommutativeAlgebra/Perfectoidization.lean`、`CLMST/`、`Inputs/`）は公開名を保つ必要があり、`scripts/move_module.py` を使う。モジュール移動なので、どの章でどこを動かすかを決めてから着手前に確認する。

### 00-map.html:139

BR2　普遍性の手書き展開の重複（Q10）

`RootedKernelSurjectivity`・`RootedPresentationSurjectivity`・`RootedIdealSurjectivity` の三箇所が、「perfectoid 化の始域を環同型で取り替えても perfectoid 化」を毎回 20 行ほどで手書きしている。同じ主張は共通側に `IsPerfectoidization.precomp_ringEquiv`（CommutativeAlgebra/PerfectoidizationFunctor.lean、10-17 から存在）として既にあり、三ファイルから import 閉包で見えることも確かめた。リファクタ計画 §13 では「共通側に新設する候補」とされていたが、新設は不要で、適用だけで済む。

### 00-map.html:143

BR3　リファクタ監査 838 行の失敗

`scripts/audit_bhatt_scholze_refactoring.lean:838` の `example` が、局所記法 `ψ` の中の `Ideal.Quotient.mk I` で環 instance の不一致（`AddMonoidAlgebra.ring` 経由と期待される `RelativeFreeDeltaRing` 上の semiring）を起こす。同じ記法が定理のソース側では通る。結論の型の前に `let := deltaDivisionSourceEvaluationAlgebra E r` があると、`I` の台が `abbrev` を開いた `MvPolynomial (σ × ℕ) P` として推論されるためと見られる。一時ファイルでの試験では、`Ideal.Quotient.mk (R := L) I` と環を明示すると監査全体が通った（`let`→`letI` の変更や module 化では直らない）。

### 00-map.html:148

BR8　どこからも使われないモジュール 173 本

BS の 1008 本のうち 173 本は、BS の外（CLMST・CommutativeAlgebra・KST・EInfinity）からも、入口（`Inputs/`）からも、root の集約からも import されない（監査だけが読む）。多いのは `Semiperfectoid/RootedExtension/Division`（38、W4 で `Andre/RootedExtension/` へ）、`…/DeltaRoot`（37）、`Delta/DividedPower`（24）、`Delta/Free`・`Free/Finite`（20）、`Prism`（19）。途中で使わなくなった経路の残りと見られる。BS-W2 では動かさず、削除するかを後で判断する（一覧は W2 の作業ツリーから再計算する）。主定理の経路に乗るのは 455 本、Rem 7.15 の照合が 265 本、root の集約だけが import するものが 115 本（W1 のスタブ 32 本を含む）。

### 00-map.html:153

BR25　docstring の工程ラベルと書式

docstring に数学の説明がなく、当時の工程ラベルだけが書かれているものが多い。共通基盤への要求番号（G1・G4・G7・G9・G10）を前提にした宣言 docstring が 30 ファイル・48 行（例：「G9-4の比較で…」）、B3・B4-x を先頭に付けたモジュール見出しが 28 ファイル（例：「B4-5：根付き…」）、A1・A1-b（André の旧工程）への言及が 99 行、F4〜F7・N3・B-I もある。番号の意味は archive の記録にしか書かれていない。概要／方針／規約／使われ方の構造を持たない一行だけのモジュール docstring が 168 ファイル、英語と日本語の一行 docstring の混在もある。ラベルと数学の言葉の対応表を一つ作れば、置き換えは機械的にできる（Codex 向き）。

### 00-map.html:157

BR26　共通基盤が BS を import している（層の逆転）

`CommutativeAlgebra/PerfectoidIdeal`、`PerfectoidIdealCover`、`PerfectoidIdealCompatibleRoots`、`AbsolutelyIntegrallyClosedPerfectoidQuotient` の 4 本が、BS のモジュールを（W1 の旧名の転送スタブ経由で）import している。少なくとも新しい名前へ付け替える必要があり、本来はこれらの所在（共通基盤か BS か）を見直すべきもの。CommutativeAlgebra は BS・CLMST 以外の利用先を確かめてから動かす。`CommutativeAlgebra/PerfectoidIdealCompatibility`（44 行）はどこからも到達しない。

### 02-delta.html:410

BR4　自由 δ 環の二重構成

`FreeDeltaRing`（\(\mathbb Z\) 上）と `RelativeFreeDelta`（任意の δ 環上）が、普遍性と表示まで二系統ある。一致は `relativeFreeDeltaStructure_int_eq`（Delta/Free/RelativeFreeIntegerComparison:19）で証明済みで、\(\mathbb Z\) 版を相対版の特殊化にできる。Lemma 2.11 の Frobenius 平坦性が \(\mathbb Z\) 版の上にあるので、規模を測ってから判断する。

### 02-delta.html:414

BR5　Frobenius が δ 射であることの二つの版

`DS.isDeltaHom_frobeniusLift`（Delta/Perfect/PerfectDeltaFrobenius:19、p 正則を仮定）は、仮定なしの `DS.isDeltaHom_frobeniusLift_general`（Delta/Basic/DeltaFrobeniusNaturality:31）に含まれる。前者の証明を後者に置き換える（名前と型は残す）。

### 02-delta.html:418

BR6　pd 包の同型の三角形と分冪構造の三重構成

raw 包 ≅ 階乗部分環、raw 包 ≅ 主 pd 表示、表示 ≅ 階乗部分環の三本は一本が残りの合成。分冪構造を局所化への引き戻しで作る構成も三回現れる。T2-1・T2-2 で多変数化するときに一本化する。

### 02-delta.html:422

BR7　根の関係とモニック関係の平行するファイル群

`DeltaRootFamilyRawCompletelyFlat`（\(X^p-b\)）と `Andre/Variants/MonicRawCompletelyFlat`（モニック）は同じ主元判定による同じ経路。統合の利益と危険を第 7 章で測る。

### 02-delta.html:426

BR32　`Delta/DividedPower/` を原典の項目ごとに分ける（2026-10-25 精読から）

74 本を §2.5 の精読で分けた五つのまとまりに沿ってサブディレクトリにする案：(1) Lemma 2.35 の 4 本、(2) Lemma 2.36 の 19 本、(4) Lemma 2.38（r=1）の 19 本、(5) 一変数の分冪多項式代数 25 本。(3) 生の \(A\{a/p\}\) と完備化の 7 本は §2.6・Prop 3.13 の部品なので、生の包を持つ `Delta/Division/` か `Prism/` の envelope の近くへ。(5) は分冪代数の一般論なので BS の外（`CommutativeAlgebra/`）へ出す選択もあるが、共有基盤の変更になる。T2-1（多変数化）を始める前に行うと、一般化した版の置き場所が決まる。BR6（同型の三角形と分冪構造の三重構成）はこの分割と同時に見る。

### 03-prism.html:132

BR33　§3 の内容を Prism の下へ集め、§7・§8 の内容を外へ出す — BS-W7（`98849e356`）で実施済み

(1) `Andre/Remark715` の有界 prism 4 本・Lemma 4.8 の 2 本・`Unoriented/` 4 本を `Prism/` の新しい話題（有界 prism）へ。依存する Remark715 の補助ファイル（`RegularPowerQuotientTorsion`、`PerfectSourceDeltaHom`、`PerfectSourceAdicRigidity`、`BoundedPrismCompatibleRootsLift` など）をどこまで一緒に移すかは依存関係で決める。(2) `Andre/RootedExtension` の Lemma 3.9 の 4 本を `Prism/Perfection` へ。(3) `Prism/Perfection` の除算系 13 本と `Prism/Perfectoid` の Cor 7.3・標数 p の 3 本を `Semiperfectoid` へ。(4) `Prism/Tensor` の置き場所（§8 の Perfectoidization 側か、prism の余積として Prism に残すか）。(5) Prism の中を話題ごとにまとめる。

### 03-prism.html:179

BR27　剛性と distinguished 性の p 正則の仮定は外せる — 2026-10-26 に BS 作業チャットで実施（`ebe9f891c`）。p 正則版・完全版・André の有界版の 22 宣言を仮定なしの一本にし、旧名は残さず呼び出し 62 か所を置き換えた（下の「旧名は仮定付きのまま残す」案は採らなかった）

`OrientedPrism.isDistinguished_of_p_regular`（Prism/Basic/OrientedPrism:65）と剛性 `existsUnique_generator_unit_of_p_regular`・`map_ideal_eq_of_p_regular`・`map_generator_mul_injective_of_p_regular`（Prism/Basic/OrientedPrismRegularRigidity）は、p 正則性を「p が Jacobson 根基に入る」ことを古典的 p 進完備性から出すためだけに使っている（確認済み）。共通基盤に既にある `mem_jacobson_bot_of_isModuleComplete`（HomologicalAlgebra/DerivedCompletion/Jacobson:39、導来完備な環ではパラメータが Jacobson 根基に入る）を `complete_p` に当てれば仮定なしで済み、原典どおり**すべての向き付き prism**で生成元は distinguished、剛性が成り立つ。完全版・p 正則版の併存（BR17）もこれで一本になる。利用は 37 ファイル。旧名は仮定付きのまま残し、仮定なしの版から導く。

### 03-prism.html:183

BR28　Lemma 3.9 を原典の形で述べる

prism の完全化は部品に分かれている：δ 環の完全化（Delta/Perfect）、完全 δ 環の PD 完備化 prism（Prism/Perfection/PerfectDeltaPDPrism）、両者を続けた環の普遍性 `existsUnique_deltaPerfectionPDCompletionHom`（旧 Andre/RootedExtension/DeltaPerfectionPDCompletionUniversal、W7 で `Prism/Perfection/PrismPerfection` へ移した）。向き付き prism \(P\) を入力に「\(\mathrm{colim}_\varphi\) の PD 完備化が \(P\) の下の普遍的な完全 prism」という原典の形の定理を Prism/Perfection に置き、環の普遍性のファイルもそこへ移す。A2・A4 で prismatic コホモロジーの完全化を扱うときの土台になる。

### 03-prism.html:187

BR29　Thm 3.10 を一つの定理としてまとめる

Thm 3.10 は (G) 商の perfectoid 性、(F の像) perfectoid 環の完全 prism 表示、(充満忠実) 射の一意持ち上げの三つに分かれ、圏同値としてはまとまっていない。逆向きは \(A_{\inf}(T)=W(T^\flat)\) ではなくその PD 完備化として作っていて、両者の比較もない。最低限、三つを並べた公開の入口（と \(W(T^\flat)\) との比較同型）を置く。圏同値まで作るかは、使い道（A0 の完全 prismatic site、Lemma 4.8）が見えてから決める。

### 03-prism.html:193

BR15　Lemma 3.9 の二系統と使われない除算の枝

prism の完全化が二系統ある。p 進完備化系の prism 層 `pCompletedDistinguishedPrism`（Prism/Perfection/PCompletedDistinguishedPrism:22）は生成元の d 進完備性を instance で仮定し、それを外せるのは既に完全な場合だけ（PCompletedPrismUniversal:52）なので、Lemma 3.9 の自明な場合しか出ていない。導来 (p,d) 完備化系の `perfectDeltaPDPrism`（PerfectDeltaPDPrism:21）は仮定なしで 15 ファイルから使われ、両者の比較同型 `deltaPerfectionPDCompletionEquiv` もある。前者の prism 層 2 ファイル（221 行）と、互いに import し合うだけの除算の枝 9 ファイル（`PCompletedDeltaDivision{Comparison,Presentation,Recovery,Repeat,Sequential,SequentialEquiv,Torsion,TorsionQuotient,PowerTorsion}`、約 830 行）は root から到達しない。環の層 `PCompletedDeltaPerfection`・`PCompletedDeltaDivision` は André が使うので残す。正本を PD 版に一本化する。

### 03-prism.html:197

BR16　Witt 商の Fontaine 比較：正則版の枝が一般版に含まれる

一般版（`WittQuotientTilt*` → `WittCompleteQuotientPerfectoid`:25 の全単射、さらに `WittDistinguishedQuotientPerfectoid`:22 で d 完備性も外れる）に対し、正則版の枝（`WittQuotientTiltKernelRegular`、`WittRegularQuotientPerfectoid`、`WittRegularQuotientFontaineKernel`、`WittQuotientFontaineIso`:84–159、`WittQuotientFontaineComparison`:90–142）は d₀ 正則と Fontaine 核進分離という強い仮定を持ち、互いの中と監査からしか使われない。障害は `WittQuotientTiltEquiv` が単射性 `wittQuotientTiltMap_injective`（WittQuotientFontaineIso:70）のために正則の枝を引き込むことだけ。単射性の部分（:23–83）を独立ファイルへ切り出せば約 300 行を削除でき、Thm 3.10 の証明が一本になる。`WittQuotientFontaineIso` という名前も、一般版では同型を含まないので中身と合わない。

### 03-prism.html:201

BR17　Lemma 3.5 まわりの並存と小さな繰り返し

完全 prism 版の剛性・同型判定は、どれも `hP.p_mul_injective` を p 正則版に渡すだけの一行のラッパー（OrientedPrismHomRigidity:20 と RegularRigidity:23、OrientedPrismIsoCriterion の 4 組、PerfectOrientedPrism:47 と RegularRigidity:44）。p 正則版を主にして、Lemma 3.5 を一ファイルにまとめる。Prism/Basic の 5 ファイルは root から到達しないので、削除ではなく公開の集約を作る案。ほかに、同じ 5 行（`f d ∈ Q.ideal` から `span {f d} = Q.ideal`）が 5 箇所、「非零でハウスドルフなら p は単元でない」が 5 箇所、「生成元で反復除算して d 進分離から単射」が 2 箇所（WittQuotientFontaineIso:35,57、OrientedPrismIsoCriterion:28）。それぞれ一般補題 1 本にする。

### 03-prism.html:205

BR18　使われない完全 prism のテンソルの枝と、標数 p の特殊化

完備テンソルの離散性は perfect δ 版 → 表示による移送 → Fontaine 版 → perfectoid 版の一本の鎖で、重複ではない。ただし perfect prism 版（`PerfectPrismCartierTensorComparison`、`PerfectPrismResidueTensorTransport`、`PerfectPrismResidueFactor`、計 347 行）は表示版の特殊化で、利用は互いの中と root の転送だけ。原典の Lemma 10.3 の証明が通るのはこちらの形なので、表示版からの 10 行程度の系に縮める。`CharacteristicPPerfectoid`・`CharacteristicPQuotient`（165 行、root から到達しない）は B3・B4 の特殊化。

### 03-prism.html:209

BR19　原典番号と置き場所の誤り

`Prism/Basic/PerfectOrientedPrism` の docstring は「Lemma 3.5・Theorem 3.10」と書くが、中身（完全 prism の生成元は distinguished、古典的 p 完備、商の p 冪ねじれは p で消える）は **Lemma 3.8** と Lemma 2.34(2)。`Prism/Residue/Prismatic*` の 5 本は一般の導来底変換で prism を使わない（HomologicalAlgebra 寄り）。`PerfectDeltaTensorRegular` が補助補題のために `PerfectDeltaCompletedTensorDiscrete` を import している（配置の逆転）。`PrismaticGeneratorPowerModPFaithful` の module docstring は別ファイルの複製。小さいファイルの統合候補：Fontaine の 3 本、Witt 商 mod p の 4 本、tilt の 3 本、Lemma 3.9 本体の 4 本。

### 07-semiperfectoid.html:103

BR30　Thm 7.14 の一段の拡大を原典の経路に揃えるか（2026-11-02 に「揃えない」で閉じた。a3-design D38）

Thm 7.14 の一段の拡大は、原典では Prop 7.11(2)（導来 prismatic コホモロジーと HT 比較）から出る。いまの Lean は Rem 7.15 の pd 計算に沿った別経路（Andre/ 直下の 46 本と、その下の根付き拡大の構成）。HT 比較は迂回しないと決めたので、A1〜A3 が揃えば Prop 7.11 を形式化して原典どおりに証明できる。そのときは今の証明を別証明として残すか（BR9 と同じ扱い）を決める。A3 までは判断しない。

### 07-semiperfectoid.html:110

BR9　B4（Thm 7.4）を Thm 7.14 の系にするか — 決定（10-25）：原典に揃える。W3 で実施済み（f4dcf1d1a・7b82e02aa）

**いまの B4 の証明.** perfectoid 環 \(R\) と全射 \(R\to S=R/J\) について、完全 prism 上で「\(J\) の元に両立する p 冪根を添加する割り算包」を作り、その完備化が p 完全忠実平坦な perfectoid 拡大 \(R\to T\) になることを示す（`PerfectPrismRootedPerfectoidExtension`）。\(T\) 上では \(J\) の生成元が根を持つので全射性が出て、それを \(R\) へ降下する（`RootedFamilyPerfectoidSurjectivityDescent`）。André の補題を使わない。

**原典の証明.** Thm 7.4 の原典の証明は、André の補題（Thm 7.14）で絶対整閉な perfectoid 環 \(T\) へ p 完全忠実平坦に拡大し（絶対整閉なら全ての元が両立する p 冪根を持つ）、\(T\) 上の全射性を降下する。

**なぜ二つあるのか.** B4 を証明した時点（10-16 18:05、`ca7121e79`）では André の補題が未証明の引用だったので、引用を避けるために André を使わない経路を新しく作った。翌日 10-17 13:18（`f9b959e61`）に André の補題が別経路で証明されたので、この理由はもう成り立っていない。原典どおりの André 経由版 `surjective_of_isPerfectoidization_of_andre`（Semiperfectoid/RootedExtension/AndreSurjectivityConditional:18）は B4 本体と同じ主張で、今は無条件に成り立つ（docstring の「sorryAx に依存」は古い）。

**差し替えると何が起きるか**（import の到達性で計算、10-25）：

- Thm 7.14 の証明は B4 も B3 も使わないので、循環は起きない。主定理はすでに CLMST 経由で Thm 7.14 に依存しているので、主定理の依存は増えない。公理は どちらも標準三公理。

- 既定のビルドから外れるのは **33 本・3,395 行**：`PerfectPrismRoot*` と `PerfectPrismRootedPerfectoidExtension` など直下 12 本、`DeltaRoot/` の 19 本（有界台の余極限、源の離散性、perfectoid 候補）、`DeltaDivisionBoundedSupportTor`、`TensorBaseChangeKernel`。代わりに降下の 3 本（`RootedKernel`・`RootedTensorBaseChange`・`RootedPerfectoidSurjectivityDescent`）と André 経由版が入る。

- このほかに、もともとどこからも使われない B4 関連のファイル（BR8 の旧「p で割る」経路など）がある。これも含めて片付けると、調査の数え方で約 67 本・6,600 行になる。

- Thm 7.14 の証明は RootedExtension/ の 109 本（割り算包の一般論、Koszul・Tor の計算、δ 代数の完全化）を使うので、これらは残る。外れるのは「任意の元の族に両立する根の列を同時に添加する」B4 固有の部分だけ。

**判断の材料.**

- 差し替える利点：証明が原典と同じ形になり、Thm 7.4 の証明が一本になる。B4 固有の 33 本（と未使用の残り）を保守しなくてよい。

- 差し替えの損失：André を使わない Thm 7.4 の証明という独立した成果がなくなる（解説 `par:bs-thm74` の後半は「原典にない経路で証明した」と書いているので書き直しが要る）。B4 が Thm 7.14 の超限反復（ω₁ 反復、後続基数による飽和）に依存するようになり、証明の依存としては重くなる。

- 今後の形式化への影響（推測）：B4 固有の部分には「完全 prism 上の \(X^p-b\) の族の prismatic envelope の離散性と平坦性」（`PerfectPrismRootSourceDiscrete`、`PerfectPrismRootPrismCompletelyFlat` など）がある。これは semiperfectoid 環の prismatic コホモロジーの計算（Ex 7.9・Prop 7.10、A3）や Prop 3.13 の特殊形に近い。A3 の設計で使える見込みがあるなら、削除せずに残す価値がある。

- 中間の選択肢：B4 本体の証明だけ André 経由に差し替え、B4 固有の 33 本は削除せずに「別証明」として root の集約から外して残す（既定のビルドを軽くし、成果は監査で保つ）。

**決定（10-25）.** 証明は原典に揃え、役に立ちそうなコードは残す。B4 の公開定理は André 経由で証明し、これまでの証明は別名の定理 `surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope` として、その構成 32 本とともに `Semiperfectoid/RootEnvelope/`（直下・`Source/`・`BoundedSupport/`）へ移す（指示書 BS-W3）。

### 07-semiperfectoid.html:131

BR10　André の一般化版（Variants）の重複 — W8（10-26）：削除せず `Andre/Variants/` 4 本にまとめた（ユーザーの決定：任意族の結果として残す）。下の旧ファイル名は `Variants/RootedExtension`・`Transfinite/Tower` の中の節

Variants の最終定理 `exists_monicRootedPerfectoidExtension`（Andre/Variants/MonicRootedPerfectoidExtension:41）は、本証明の `Transfinite.exists_monicFamilyRootedPerfectoidExtension`（Andre/Transfinite/FamilyExtension:62）と仮定のまとめ方以外は同じ型（確認済み）。本証明は一元の根添加と飽和、Variants は有界台の余極限で一段に作る別経路。一元版 `exists_monicRootPerfectoidExtension`（Variants/FiniteMonicRootedExtension:94 と Transfinite/SingleRoot:50）、補助補題 `isCompletelyFaithfullyFlat_self`・`isCompletelyFaithfullyFlat_ringEquiv` も重複。Variants の Arbitrary 系列 14 本ほかは、本証明の系として 1 行で出るので削除できる。補助補題は CommutativeAlgebra/CompletelyFlat へ移す。

### 07-semiperfectoid.html:135

BR11　行き先のない照合と旧経路（Rem 7.15、Variants） — W8（10-26）：Remark715 は Rem 7.15 の結論を証明していないと分かったので `Andre/PowerRootEnvelope/` に改名して全部残し、Variants も残した。`BoundedPrism*`・`PerfectPrismBoundedTarget*` は W7 で `Prism/` へ移した

Rem 7.15 のうち最終 3 定理にも Thm 7.14 にも到達しないものが 28 本・3,421 行（Frobenius 引き戻しの PD 普遍性の別経路、`PerfectPrismVarpi*`・`PowerRootPrismMonic*` の一部、監査 4 本など）。Variants の `MonicRaw*` 10 本（約 1,500 行）は旧「補助 raw φ(f)/p 包」経路でどの定理にも至らない。Variants の集約 `Variants/MonicRootedExtension`（import だけ約 100 行）が、これらを root へ流し込む唯一の経路。集約を最終定理だけの import に縮め、残りを削除する。ただし削除の前に、`BoundedPrism*`・`PerfectPrismBoundedTarget*` が A0 の Lemma 3.7・4.8 の出発点として使えるか確かめる（第 4 章）。

### 07-semiperfectoid.html:139

BR12　条件付き版と降下の重複系列 — W3・W7・W8：`AndreSurjectivityConditional` は B4 の正規の入口として `Semiperfectoid/Surjectivity` に入った。`AndreCompatibleRootsConditional` は W8 で削除した（監査の該当行も外した）

`AndreSurjectivityConditional`・`AndreCompatibleRootsConditional` はどこからも import されず、監査 `audit_bhatt_scholze_andre_conditional` だけが読む。docstring の「sorryAx に依存」は古い。BR9 で採るなら B4 の正規の入口に改名し、採らないなら削除する。`RootedKernelSurjectivity → RootedTensorBaseChangeSurjectivity → RootedPerfectoidSurjectivityDescent` は条件付き版からしか使われず、B4 本体は別の系列（`RootedPresentation → RootedFamilyPerfectoidSurjectivityDescent`）を使う。また `Semiperfectoid/PerfectoidizationSurjectivity`:13 と `Semiperfectoid/TorsionFreeQuotientSurjectivity`:19 は、仮定（p ねじれなし）を外した `surjective_of_isPerfectoidization_of_adic_complete_quotient`（SemiperfectoidSurjectivity:51）が既にある旧い適用形で、監査からしか使われない。

### 07-semiperfectoid.html:143

BR13　手で繰り返している証明の型

(a)「商の導来 H⁰ → 高次の消滅 → IsGE/IsLE → single との同型」の 8〜11 宣言の骨格が 6 回（`DeltaRootSourceQuotientDerived`、`DeltaRootFamilySourceQuotientFlat`、`DeltaRootBoundedSupportQuotientFlat`、`MonicPrismaticQuotientDerived`、`ArbitraryMonicPrismaticQuotientDerived`、`PowerRootQuotientDerived`）。「L 線形同型を商写像の全射性で Q 線形に上げる」構造も同じ 6 ファイルで手書き。汎用補題 1 本で置き換えられる。(b)「perfectoid 環を完全 prism の商として表す」約 12 行が 6 か所（Semiperfectoid の 2 本、Transfinite/SingleRoot、Variants の 2 本、Prism/Perfectoid/PerfectPrismQuotientPerfectoidization）。「零環か、完全 prism P と R ≃ A/d がある」という補題 1 本にまとめる。(c) SourceDiscrete・PDCompletelyFlat・PerfectoidCompletelyFlat の三段が 4〜5 系列（B4、André 有限、Arbitrary、DeltaAlgebra、PowerRoot）で並行。パラメータ化した一系列にまとめる案は規模が大きく、調査が要る。

### 07-semiperfectoid.html:147

BR14　ライブラリ内の監査ファイル — W8（10-26）：`noncomputable section`・`meta section` を閉じずに使うので統合できず、`Andre/PowerRootEnvelope/Audit/` の 4 本として移した。`scripts/` への移動はまだ

`Andre/Remark715/…/Audit.lean` など 4 本は `#print axioms` を並べた監査で、ライブラリの中にある（W2 の初回ビルドが一覧の旧名で止まったのもこれ）。`scripts/` へ移す。

### 08-perfection.html:105

BR31　Prop 8.13 の環版を導来版の系に置き換える（A7 の後）

Prop 8.13 の環版（Perfectoidization/ の 4 本、約 600 行）は、HT 比較なしで示すために普遍性を手で組み立てている。原典の導来版は Δ の対称モノイダル性から一行で出て、A7 で形式化する。そのときは、環版を導来版と Cor 8.14 の系として述べ直し、今の証明を外す（主張と型は保つ）。

### 08-perfection.html:111

BR20　有限直積の perfectoid 性が E3 に依存している

`isIntegralPerfectoid_finPi`（Perfectoidization/PerfectoidFiniteProduct:21、「perfectoid 環の有限直積は perfectoid」）は、E3 から得た perfectoid 化の存在 `Inputs.exists_perfectoidization_of_integral` を使って証明されている（確認済み）。CLMST の 3 ファイル（`PerfectoidFiniteProductTor`、`Prop247ConstantRankExcision`、`KLAicTorFromExcision`）が使う。主定理はもともと E3 に依存するので新しい sorry ではないが、BS-0 の消費経路の一覧（stage2 §1）に載っていない E3 の使用箇所。四条件（Fontaine 核の単項性、p 完備性、Frobenius の全射性）は成分ごとに確かめられるので、E3 なしで直接示せるはず。E3 の使用箇所を本当に必要な二つ（存在と excision）に絞るために優先度が高い。

### 08-perfection.html:115

BR21　IsPerfectoidization の API を足して手書きの展開を置き換える

普遍性 `hf.2` を直接展開している箇所が、`PerfectoidFiniteProduct`:35、`PerfectoidizationSurjectiveMap`:40,42、`PerfectoidizationTensorCompatibility`:66–81、`PerfectoidizationBaseChange`:38,47、`CompletedTensorPerfectoidUniversal`:92、`PerfectoidizationCompletedTensorCompatibility`:154 などにある。既存の `lift`・`lift_unique`・`map` で書けるほか、共通側に二つ足すと重複が消える：(a) `IsPerfectoidization.hom_ext`（a∘f = b∘f なら a = b）、(b)「u : A → A′ が perfectoid な標的への写像を一意に延ばすなら、f′ が perfectoid 化 ⇔ f′∘u が perfectoid 化」という移送補題。(b) で `precomp_ringEquiv`、完備化への移送 2 本、`completedTensorPerfectoidLift_isPerfectoidization` が数行になり、`CompletedTensorPerfectoidization`:56 と `CompletedTensorPerfectoidUniversal`:28 の逐語複製（約 30 行）も消える。共通側（CommutativeAlgebra）の変更なので、他の利用先がないことを確かめてから。

### 08-perfection.html:119

BR22　底変換・三角図式・Prop 8.13 底変換の共通化と、二つのテンソルのモデル

`PerfectoidizationBaseChange`:28 と `PerfectoidizationTensorCompatibility`:55 は、係数テンソルの持ち上げとテンソル積の帰納法による同じ型の証明（各 70 行ほど）。そのままでは特殊化にならないので、「C⊗_P D からの射は左右の制限で決まる」外延性補題と持ち上げの補題を共通にする。`prop813BaseChangeMap` も三角図式版の特殊化に見える（推測）。また perfectoid 環のテンソルの perfectoid 化に、Witt 余積のモデル（`Perfectoidization/WittPresentation/` ほか約 720 行）と完備テンソル H⁰ のモデルが並んでいる。Witt モデルの用途は mod p 全単射性と根付き拡大の 2 つだけで、前者は完備テンソル側の普遍性から直接出る見込み。後者が Witt モデル固有の性質を使っていないかの調査が要る。

### 08-perfection.html:123

BR23　公開の形

Prop 8.13 環版の 4 本（`Prop813PerfectoidBaseChange`、`PerfectoidizationCompletedTensorCompatibility`、`PerfectoidizationTensorCompatibility`、`CompletedTensorPerfectoidUniversal`）は証明済みだが root から到達せず、既定のビルドに入っていない（監査だけが読む）。到達点として挙げている結果なので、集約から公開する。`isIntegralPerfectoid_of_ringEquiv`（Prism/Perfectoid/PerfectoidRingEquiv:21）は純粋に可換環論の事実で 21 ファイルが使うので、CommutativeAlgebra/IntegralPerfectoid の近くへ移す。`PerfectCoefficientTensor`（22 行、alias だけ）は利用 4 箇所を直接の名前に切り替えて消せる。

### 10-almost.html:91

BR24　almost の言葉で述べ直す

Almost/ の supported quotient の系列（`PerfectoidizationSupportedQuotientKernel`:50,77,98、`…Linear`:30、`PerfectoidizationImageComparison`:30–55）は、「\(J_{\mathrm{perfd}}\) の全元が x を消す」を毎回手で書いている。共通側の `IsAlmostZero`・`IsAlmostIso`（CommutativeAlgebra/Almost/Zero:25、Morphism:34）で述べ直せる。CLMST 側の利用も変わるので規模は中。`lemma103_perfectoidTensor` の宣言 docstring は一般の perfectoid テンソルを「Lemma 10.3」と呼んでいるが、原典ではこれは Lemma 10.3 の証明中の主張（module docstring は正しい）。`Almost/PerfectoidAlmost`（17 行）は集約だけのファイル。

