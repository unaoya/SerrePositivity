# K-L4：導来圏と幾何の基盤

作成日：2026-10-18。状態：L4a 途中。§26 の設計変更は採用済み。一般 dg 圏の半自由分解と K-flat 性の供給を DGResolution/ で実装する（§27）。

## 0. 目的と所有範囲

- レーン名は K-L4（導来圏と幾何の基盤）。
- 正本は k-theory-kst-route.md §2.4・§2.7・§4 D4・§5 A・§10-7・§13。
- 基盤の優先順位は foundations.md に従う。
- 本レーンは D_qc(X;H)、Perf(X;H)、台つき部分圏、局所化、降下を所有する。
- K 群、K スペクトル、局所化不変量の実装には依存しない。
- 導来 blowup、射影束、KST §3 の半直交分解は K-L5 の所有とする。
- 既存 DifferentialGraded/・PerfectComplex/・CategoryTheory/・KTheory/ は読むだけとする。
- 実装は SerrePositivity/KST/DerivedGeometry/ に置く。
- 名前空間は SerrePositivity.KST.DerivedGeometry に固定する。
- 集約は SerrePositivity/KST/DerivedGeometry.lean とする。
- ルートへの変更は集約の public import 一行だけとする。
- 他レーンの計画・索引・README は編集しない。

## 1. 仮定と数学的対象

- A は可換環、H は単位的結合 A 代数とする。
- H の像と構造層の作用は可換とする。H 自体の可換性は要求しない。
- 幾何の主定理は準コンパクトかつ準分離な A スキーム X について述べる。
- KST に適用する Noether スキームはこの仮定を満たす。
- 有限アフィン開被覆の存在は準コンパクト性から得る。
- 二つのアフィン開の交わりの準コンパクト性には準分離性を使う。
- 交わりそのものがアフィンであるとは仮定しない。
- 一般の交わりでは有限アフィン細分を選択する。
- H_X は U ↦ H ⊗_A O_X(U) の層化で作る係数環層とする。
- この前層がすべての開で既に層だとは主張しない。
- D_qc は H_X 加群層の導来圏内で、忘却後の全コホモロジーが準連接な対象とする。
- Perf は局所有限射影複体の模型と compact 対象の同一性を証明してから同定する。

## 2. 原典と照合表

- Bondal–van den Bergh, Generators and representability of functors in commutative and noncommutative geometry, Thm 3.1.1。
- 同 Thm 3.1.1 の compact = perfect と単一 compact 生成元を分けて証明する。
- Neeman 1992, The connection between the K-theory localisation theorem of Thomason, Trobaugh and Yao and the smashing subcategories of Bousfield and Ravenel, Thm 2.1。
- 原典番号の訂正：Cor 3.2.3 は Bondal–van den Bergh の番号。Neeman 1992 は Thm 2.1。Toën §3.2（p.34）もこの区別で参照している。
- Thomason–Trobaugh, Higher algebraic K-theory of schemes and of derived categories, §3。
- 同 3.19：開部分の補集合に台を持つ perfect 複体の切除に対応する。
- 同 §8・8.1：Zariski Mayer–Vietoris の圏的入力を切り出す。
- Toën, Derived Azumaya algebras and generators for twisted derived categories, §3.2。
- Toën の導来係数の記述と離散係数の特殊化を区別する。
- 原典の定理を未証明フィールドとして構造体へ入れない。
- 原典の参照は証明の出典であり Lean の追加公理ではない。
- 原典番号の詳細・必要な補題は各工程の節でも指定する。

## 3. 現在地と受入条件

- 現在地：L4a の係数環層・準連接性・開埋め込みの比較と、アフィン大域切断の忠実性・同型反映は証明済み。任意 dg 圏の段階分解、Hom の K-flat 性、増大関手の各次数全射性・準同値性・H⁰ 同値、前三角化の三角同値、分解後の path 商と元の指定 Verdier 商の tria 比較を実装済み。層の DerivedDG・DqcDGModel も平坦分解後の商へ移行済み。商自体の H⁰ と Mathlib の導来圏の同値、Perf、アフィン係数加群圏の同値、導来降下は未完了。
- L4b の入力である層の随伴と導来忘却は実装済み。L4b の導来随伴・生成・T1′、L4c、L4d、L4e は未実装。
- 最新の検証済み保存単位は対象ビルドと所有 namespace の698宣言の公理監査に成功。許容公理は標準3公理のみ、KTheory import なし。
- 既存 dg 基盤と Mathlib の接続点を確認中。
- 層レベルの降下と導来局所化の交換は未証明として管理する。
- 保存単位ごとに対象 lake build を実行する。
- 保存単位ごとに scripts/audit_kst_derived_geometry.lean を実行する。
- 許容公理は propext・Classical.choice・Quot.sound のみ。
- 到達可能な sorryAx・追加公理を検出した単位は検証済みとしない。
- 工程の完了時には全体ビルドを実行する。
- 並行作業で import 閉包が破損した場合は回避実装を作らず報告する。
- コミットは検証済みの所有ファイルだけを git commit --only で行う。
- 実施経緯はこの計画に追記せずコミットメッセージに記録する。

## 4. 設計上の決定：層から導来圏へ

- 第一層は実際の環層と加群層を使う。抽象圏の名前だけを D_qc としない。
- 係数構造は O_X → H_X の環層射で表す。
- 加群層の圏は Mathlib の SheafOfModules を使う。
- 係数忘却は SheafOfModules.restrictScalars を使い、完全性・小さい余極限の保存を証明済み。
- O_X 加群層は AlgebraicGeometry.Scheme.Modules を使う。
- 非有界複体は CochainComplex C ℤ を使う。
- 導来局所化は Mathlib の DerivedCategory と Q を接続点とする。
- 選択された導来圏の Hom 宇宙は HasDerivedCategory で明記する。
- 標準局所化は必要な宇宙で実在する構成を使う。
- D_qc は準連接なコホモロジーを条件とする充満部分圏で定義する。
- 各項が準連接な複体の導来圏との同値は一般の qcqs では成立しない。BvdB Thm 3.1.3 直後の注意を参照。
- 特に非有界の場合にこの同値を定義的等式として扱わない。

## 5. 接続点：Mathlib の準連接層

- Mathlib.AlgebraicGeometry.Modules.Presheaf は Scheme.ringCatSheaf を与える。
- Mathlib.AlgebraicGeometry.Modules.Sheaf は Scheme.Modules を与える。
- Scheme.Modules はアーベル圏・Grothendieck アーベル圏・極限と余極限を持つ。
- Mathlib.AlgebraicGeometry.Modules.Tilde はアフィン上の tilde 関手を与える。
- isQuasicoherent_iff_isIso_fromTildeΓ は準連接性を大域切断からの復元で判定する。
- AlgebraicGeometry.tildeEquiv は ModuleCat R と Spec R の準連接層の同値である。
- 準連接性の開制限の保存も同ファイルに存在する。
- SheafOfModules.IsQuasicoherent.of_coversTop は準連接性の局所判定に使う。
- これらはまずアーベル圏・層の定理であり導来圏の同値そのものではない。
- アフィン上の導来同値には切断の非有界導来計算との接続が必要である。
- 有限アフィン被覆のデータは実際の開集合と被覆の証明を保持する。
- 被覆の添字はアフィン開の Finset の要素とする。Fin n への再添字は必要時に行い、空被覆も許す。

## 6. 接続点：既存 dg 基盤

- DGCategory は A 線形な dg 圏の構造を与える。
- modulePerfect は代表加群の finite cell の retract として定義されている。
- moduleCompact_iff_perfect は導来 dg 加群の compact 性と perfect 性の一致を与える。
- この定理はスキームのコンパクト生成を既に証明しているわけではない。
- ringDerivedEquivalence は一対象可換環の場合の Mathlib 導来圏への接続点である。
- 非可換 H ⊗_A O(U) への適用は A 線形な一対象 dg 圏を用意して行う。
- 係数環自体を可換と仮定してこの問題を消さない。
- localPerfectQuotientEquivalence は localKFlat の仮定付きである。
- この仮定の充足・置換の選択は幾何の局所化との比較後に検証する。
- 既存の係数変更・導来 tensor はアフィン計算に用いる。
- 既存 PerfectComplex の環上の有限射影複体も比較先として調べる。
- K0Comparison・K 理論のモジュールは本レーンから import しない。

## 7. §10-7：実装前の文言と証明方針

- 検証する文言：有限アフィン被覆上の係数加群層の降下模型を導来化すると D_qc(X;H) と同値になる。
- この文言で「降下」はまず層または複体の段階での有効降下を意味する。
- 導来圏上の同型と三重交差の cocycle だけからなる通常の圏の極限は採用しない。
- その通常の極限は写像の高次情報を失うため、D_qc の降下と同一視できない。
- 複体の段階では鎖同型による strict descent と各次数の加群層の有効降下を使う。
- 貼り合わせた微分は局所微分の両立性から定義し、d² = 0 は層の局所性で証明する。
- 射も各次数で貼り合わせ、複体の降下圏と大域複体の圏の同値を得る。
- 準同型性はコホモロジー層の開制限で局所的に判定する。
- この同値の両側を同じ局所的準同型のクラスで局所化する。
- 局所化の普遍性により導来圏の同値を得る。
- 準連接性は開被覆上で局所的なので D_qc の充満部分圏へ制限する。
- この方針だけでは局所 perfect 代表を鎖同型で貼り合わせられるとは言えない。

## 8. §10-7：有限被覆の MV 帰納

- 帰納の変数は有限アフィン被覆の枚数とする。
- 一枚の場合はアフィンの加群・準連接層の比較を使う。
- 帰納段階は X = V ∪ U とし、U を最後のアフィン開とする。
- V は残りのアフィン開の合併である。
- V ∩ U は準コンパクトで有限アフィン細分を持つ。
- V ∩ U の被覆枚数が元より小さいとは限らない点に注意する。
- 従って単なる被覆枚数だけの循環した帰納証明は書かない。
- MV の層の完全列・導来制限と押し出しの随伴から二開被覆の貼り合わせを先に証明する。
- 台つきの compact 生成元をアフィン開の補集合から構成する。
- Neeman 型の compact の持ち上げを使い perfect と compact の比較を進める。
- 有限被覆の Čech 計算には交わりのアフィン性を暗黙に用いない。
- 一般の交わりには導来切断を使い、アフィン細分との比較を別途証明する。

## 9. L4a：具体的な工程

- 環層の係数構造とその加群層の型を固定する。
- 有限アフィン開被覆の型を固定する。
- 加群層の strict descent の対象・射・合成を構成する。
- 大域層からの制限関手を定義する。
- 加群層の貼り合わせ関手と単位・余単位を構成する。
- 複体へ次数ごとに持ち上げる。
- 準同型の局所判定を証明する。
- 導来局所化の比較を構成する。
- 準連接コホモロジーの部分圏へ同値を制限する。
- アフィン dg 模型との比較関手を構成する。
- 局所 perfect 性を充満部分圏の対象条件として定義する。
- 完了条件は型の定義だけでなく比較の証明を含む。

## 10. L4b T1：自由・忘却と生成

- 原典対応は Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
- 自由関手 F(P) = P ⊗^L_O H_X を構成する。
- 加群の左右の規約は全体を通じて固定し、非可換の場合にも明記する。
- 忘却 U は係数を忘れ O_X 複体を取る。
- F ⊣ U を Hom の自然同型から構成する。
- U が準同型を反映することをコホモロジー層で示す。
- U が導来圏で保存的であることを cone の消滅で示す。
- U が必要な余積を保存することを層・複体の計算で示す。
- 各 P が compact なら F(P) も compact であることを随伴から示す。
- 全 P と全シフトから F(P) への Hom 消滅が U(M) = 0 を含意する。
- O_X の compact 生成から M = 0 を結論する。
- 随伴・保存性を仮定するだけの theorem を T1 の完成としない。

## 11. L4b T1′：局所有限射影複体

- アフィン U 上の係数環を H ⊗_A O_X(U) とする。
- 有限射影加群の有界複体の各項と微分を実際のデータとして持つ。
- 有限自由複体の retract と有限射影複体との比較を証明する。
- 既存 dg finite cell・retract API との同値を構成する。
- 局所 perfect 性の開制限に関する安定性を証明する。
- 有限アフィン被覆上の局所判定が被覆に依存しないことを示す。
- 大域 compact 対象の開制限が compact である条件を確認する。
- 局所 perfect から大域 compact への方向は二開 MV の帰納を用いる。
- Rj_* の余積保存には準コンパクトかつ準分離な開埋め込みを使う。
- Bondal–van den Bergh Cor 3.2.3 の使用前に必要な生成条件を証明する。
- H の A 上平坦性をこの段階の仮定に追加しない。
- 完了時に Perf の二つの模型と dg 増強の対応を表に記載する。

## 12. L4c T2：局所化

- 原典対応は Neeman 1992 Thm 2.1 と Bondal–van den Bergh Cor 3.2.3。
- U ⊂ X は準コンパクト開、Z はその閉補集合とする。
- D_Z は U への導来制限が零となる対象の充満部分圏とする。
- 局所化の核とコホモロジー層の台条件の一致を証明する。
- D_Z の局所化部分圏としての閉性を証明する。
- 台つき compact 生成元の存在を証明する。
- 制限と導来押し出しの随伴を構成する。
- 開埋め込みの随伴の余単位が同型であることを示す。
- D(X;H)/D_Z ≃ D(U;H) を Verdier 商の普遍性で証明する。
- compact 部分への制限と冪等完備化の位置を明記する。
- 全充満性と稠密性を本質的全射性と混同しない。
- dg 商との同値は localKFlat 条件を実際に充足させて構成する。

## 13. L4d T3：切除と Čech

- 原典対応は TT 3.19・8.1、Toën §3.2。
- 閉集合の近傍で同型となる開制限について台つき圏の同値を証明する。
- 二開被覆の MV を層複体の導来関手から構成する。
- 三角圏の通常の pullback を導来 pullback と同一視しない。
- 必要な dg 模型の写像複体に対する homotopy pullback を構成する。
- Čech の各次数を被覆添字の列で記述する。
- 面・退化射と増大射の恒等式を証明する。
- 被覆細分に対する自然性を証明する。
- 有限被覆の反復 MV と Čech の比較を証明する。
- 空交差・空スキームでの対象と制限も明示的に扱う。
- 結果は圏のレベルで公開し K 理論の実装を import しない。
- K-L8 への入力は所有範囲内の公開宣言で供給する。

## 14. L4e：平坦係数の RHom 計算

- 対象は O_X 上 perfect な P,Q と A 上平坦な H。
- まず局所有限射影複体について Hom と ⊗_A H の交換を証明する。
- 有限射影性により Hom の基底変換を有限自由の retract へ帰着する。
- 複体の微分と符号の両立を証明する。
- Čech の各項で得た同型の制限に対する自然性を示す。
- 有限アフィンの交わりが非アフィンの場合は導来切断を使う。
- 平坦性で tensor が準同型を保存することを使う。
- 有限 Čech の適切な模型と tensor の交換を証明する。
- 非有界無限積と tensor の交換を無条件に使わない。
- RHom_H(P ⊗ H,Q ⊗ H) ≃ RHom_O(P,Q) ⊗_A H を得る。
- この同型の O_X 線形性・A 線形性・合成との両立を公開する。
- K-L5 の基本 Hom 計算へ接続する。

## 15. 検証・コミット・停止条件

- 対象ビルドは set -o pipefail を設定して終了コードを確認する。
- 監査は所有 namespace の全公開宣言と推移的依存の公理を調べる。
- 主要宣言が監査対象に存在することも確認し空の監査を成功扱いしない。
- 計画の主要宣言の表は実装済みと未実装を区別して更新する。
- 保存単位が失敗した場合は成功と報告しない。
- 全体ビルドは工程の区切りで行う。
- 共有ルートには既存の他レーンの変更があるためコミットの差分を分離する。
- 分離できない変更は不用意に自分のコミットへ含めない。
- amend・rebase・reset は実行しない。
- 紙の未確認事項は計画に文言と証明方針を記録して報告した後に進める。
- 設計変更が必要な場合は根拠を明示して提案する。
- 完了・設計変更提案・import 閉包の破損以外で自主的に作業を打ち切らない。

## §13 決定11：§10-7 の厳密降下と層の dg 増強の区別

- 根拠：[Bondal–van den Bergh 原典](https://arxiv.org/pdf/math/0204218)、pp.8–9（論文頁）。
- Thm 3.1.1 は D_qc(X) について compact = perfect と生成を述べる。
- Thm 3.1.3 は準コンパクトかつ分離の仮定で D(QCoh(X)) → D_qc(X) の同値を述べる。
- 直後に、分離を準分離へ弱めると有界の場合にも偽となることを明記している。
- したがって、各アフィン上の環の加群複体を鎖同型で厳密に貼り合わせる模型は慎重に扱う。
- 各項の環加群を tilde で層に直し厳密に貼り合わせると、各項が準連接な大域複体になる。
- この圏を通常の準同型で局所化するだけでは一般に D_qc(X) を復元できない。
- H = A の場合に既に問題があるため、H の平坦性を加えても解決しない。
- 初期方針の「層・複体を貼り合わせて局所化する」は、任意の加群層の複体なら利用できる。
- しかし、その各チャートを環の加群複体に置き換える操作との交換は別の実質的な定理である。
- 任意の加群層の複体ではアフィン上でも各項を環の加群と同一視できない。
- 比較すべき対象は各項の準連接性ではなくコホモロジーの準連接性である。
- 現在実装した CoefficientSheaf.Dqc はこのコホモロジー条件を採っており変更不要。
- CoefficientSheaf は一般の環層と構造層射を扱う基礎型。H_X の具体的構成は coefficientSheafOfMorphism が与え、構造層の中心性も別定理で証明済み。
- 一般の CoefficientSheaf について無条件の compact 生成を主張していない。
- D4 の「有限アフィン被覆上の加群の降下」を厳密降下と読んだ実装には進まない。
- 正本 §13 決定11：dg 増強は H_X 加群層の複体の dg 圏を acyclic で dg 商したものに取る。
- Perf と D_qc はこの dg 商の充満部分圏として扱う。
- アフィン導来 dg 加群圏の Čech ホモトピー極限との比較は定義にせず、必要な段階の定理とする。
- 対象の遷移は導来同値、射の計算には写像複体とその高次の両立性を保持する。
- 通常の三角圏の同型と cocycle だけを持つ pullback は使わない。
- Čech のホモトピー極限との比較が必要なときは、層の dg 商からの比較定理を独立に証明する。
- 局所 perfect な対象の対応も、定義による同一視で済ませない。
- この決定は K 理論への依存・引用・公理・sorry を追加しない。
- 分離性を追加しないので KST の非分離 qcqs の範囲を維持する。
- 層の複体から定義する場合にも、アフィン環の dg 加群との比較は導来化後の定理として必要になる。
- [Toën 原典](https://www.math.univ-toulouse.fr/~btoen/dgazumaya.pdf) §3.2、pp.32–35 に対応を確認した。
- Toën Prop 3.9 は compact local generator の Zariski 貼り合わせを述べる。
- 同 p.34 の局所計算はアフィン開にわたる dg 圏の Holim を明示している。
- 同 p.35 の帰納段階は二開被覆の homotopy cartesian square を用いる。
- 交わり W の被覆枚数に対する帰納はせず、アフィン側から W への compact の持ち上げを使う。
- 持ち上げには Neeman Thm 2.1 と BvdB Cor 3.2.3 の E ⊕ E[1] を使う。
- そのため、有限被覆の枚数が単調に減らないという初期の注意にも整合する。
- dg 増強の実装は層の複体の dg 圏と acyclic の dg 商を起点とする。アフィン加群の関手比較は別の入力補題として整備する。
- 厳密なアフィン環加群複体の模型は採らない。任意の加群層の複体に基づく現在の Dqc の定義・係数忘却は正本の決定と一致する。
- L4a は未完了、T1・T1′・T2・T3・RHom 比較も未完了とする。T1 の層の随伴と導来忘却の実装だけで T1 完了とはしない。
- 今回の補助補題の検証を上記主定理の証明と数えない。

## 16. 係数忘却の接続と残りの証明

- 任意の係数環層 B について、層の忘却は加法的・完全・保存的である。
- 層の忘却は、加群の宇宙以下の添字の余極限を保つ。
- 証明は基礎アーベル群の層への忘却を介して行う。
- 基礎アーベル群の層への忘却の余極限保存は、前層の余極限を層化することで証明する。
- 反射的局所化の余単位が自然同型であることを使い、層化前の保存性を層へ移す。
- 切断関手が任意の余極限を保つという誤った主張は使わない。
- 層の係数忘却の左随伴は、恒等な基礎空間上の加群層の引き戻しから構成する。
- この左随伴の存在を未証明フィールドとして入力しない。
- 層の自由関手の完全性は主張しない。
- 非平坦な係数では、層の自由関手を複体へ項別に適用しただけでは左導来関手にならない。
- 導来忘却は完全な関手の導来化として構成する。
- 複体のコホモロジー比較を局所化による前合成の全忠実性で導来圏へ降ろす。
- 導来忘却の保存性はコホモロジーによる同型判定と層の忘却の保存性から証明する。
- 導来忘却が忠実であるという強すぎる主張はしない。
- 係数つき Dqc の対象条件は、導来忘却の像が通常の DqcO に属する条件と同値である。
- この同値により Dqc 間の忘却関手を構成し、同型反映性も移す。
- 導来忘却の余積保存には、導来圏の余積の構成との比較をさらに証明する必要がある。
- T1 の残りは H_X のアフィン模型・準連接性との比較、導来自由関手と随伴、導来余積保存、通常の Dqc の生成である。
- T1′ の局所有限射影複体との一致と、L4a のアフィン dg 模型への比較も別に残る。
- これらを既存の dg 加群圏の定理を名前だけ変更することで代替しない。

## 17. 具体的係数環層 H_X とアフィン比較の接続

- 入力は単位的結合 A 代数 H と、実際の構造射 f : X → Spec A。
- 構造射の大域切断の写像を Γ(Spec A,⊤) ≃ A と合成して A → Γ(X,⊤) を得る。
- 各開の A 代数構造は、この大域写像を構造層の制限写像と合成して作る。
- 制限写像の A 線形性を前層の合成則から証明する。
- 異なる構造射による A 作用を暗黙の大域インスタンスとして混在させない。
- 係数テンソル前層の値は H ⊗_A O_X(U)、制限は id_H ⊗ res。
- テンソル前層の恒等射・合成則は純テンソルによる帰納で証明する。
- H の可換性と A 上の平坦性はこの構成・前層法則に不要。
- 構造層からの単位は r ↦ 1 ⊗ r。
- H の定数前層からの写像は h ↦ h ⊗ 1。
- 定数前層が層であるという仮定は置かない。
- 二つの包含は A の作用について一致する。
- O_X(U) の像が中心的であることは純テンソルの積と加法による帰納で示す。
- 環の圏 RingCat でテンソル前層を層化して H_X を得る。
- 構造層の環層射は、右因子への包含と層化の単位を合成して作る。
- 比較射は局所全射であり、大域切断上の全射性は主張しない。
- 層化後の中心性は比較射を使って局所的にテンソル前層へ持ち上げ、層の分離性で示す。
- これにより各開の H_X の切断の O_X(U) 代数構造も実際のデータとして得る。
- H_X の任意の開 U の切断が H ⊗_A O_X(U) と同一であるとは定義しない。
- アフィン U 上の比較射が同型であることは別途必要な定理。
- Mathlib の tilde M と基本開上の IsLocalizedModule.Away を接続済み。任意の加群 M について基本開切断のテンソル表示の線形同型と純テンソルの計算式を証明済み。
- テンソル表示の制限射への自然性と層化比較は実装済み。一般の A → R に対する底変換と、基本開・全体の環切断の同型判定も §21 の通り実装済み。
- H = A の場合の構造層の回復は tensorCoefficientSelfIso として証明済み。一般の A → O_X(U) の底変換への自然性は別途確認する。
- このアフィン同定なしに既存 dg 加群圏の moduleCompact_iff_perfect を適用しない。
- 原典対応は KST 経路 §4 D4・§2.4 と Toën Derived Azumaya §3.2。

## 18. アフィン基本開での計算と残る接続

- Spec R 上の sectionBaseMap は Mathlib の標準の algebraMap R O(U) と一致する。
- sectionAlgebra も、標準の切断の代数構造と実際の構造として一致する。
- tilde M の D(f) 上の切断への写像は IsLocalizedModule.Away f を満たす。
- O(D(f)) が R の f による局所化であることを使い、加群局所化を底変換へ直す。
- これにより O(D(f)) ⊗_R M から tilde M の切断への線形同型を得る。
- テンソルの因子を交換して M ⊗_R O(D(f)) の形にする。
- 純テンソル m ⊗ s は s 倍した m の標準切断へ送られる。
- この計算に M の平坦性・有限生成性・射影性を要求しない。
- この線形同型そのものと、係数環層の環としての比較は異なる宣言で扱う。
- 制限への自然性と層化との比較は §19 の通り、基礎環 A から R への底変換は §21 の通り実装済み。
- H = A の係数前層は構造層と自然同型で、すでに層条件を満たす。
- その層化の比較も同型なので、H = A の係数環層は構造層へ標準的に戻る。
- これらを L4a 全体の降下比較や、T1 のコンパクト生成の証明と混同しない。

## 19. 自然な層化比較と基本開上の環同型

- 任意の R 加群 M に対し、各開 U で M ⊗_R O(U) から tilde M の切断へ写像を作る。
- 純テンソル m ⊗ s の像は s 倍した標準切断とする。
- 制限に関する自然性は加群層の半線形な制限と標準切断の両立から証明する。
- 基本開でこの写像を既存の局所化の線形同型と同定する。
- 開基上で単射・全射な前層射は局所単射・局所全射になるという一般補題を実装する。
- これを Spec R の基本開基に適用し、テンソル前層と tilde の局所全単射性を得る。
- 加群圏で層化すると tilde M に自然同型になる。
- この同型と層化の単位の合成が、指定した前層比較に等しいことも証明する。
- 係数環前層と加群テンソル前層の基礎加法群を自然同型で比較する。
- 切断の二つの代数構造の等式を明示的に移送し、純テンソルとの両立を示す。
- 環および R 加群から加法群への忘却が層化と可換であることを用いる。
- 基礎集合への忘却と可換な関手が局所全単射性による層化の同値を保存する補題を証明する。
- 合成により係数環層の基礎加法群と tilde H の基礎加法群の層の自然同型を得る。
- この自然同型と層化前の比較射の可換式を証明する。
- 基本開で tilde の比較が同型なので、係数環の層化の比較も基礎加法群上で同型となる。
- 環準同型の基礎写像の全単射性から、基本開で環の同型であることを得る。
- D(1) = Spec R により、全体の切断の比較も同型となる。
- この段階では H の平坦性・可換性・有限性を一切要求しない。
- 原典の接続は KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
- 基礎環は R、スキームは Spec R とする標準構造射での結果である。
- 任意の A → R に対し H_R = H ⊗_A R と置いた場合との環層の比較は §21 の別定理で証明済み。
- 加法群の層の同型だけでは O 加群としての準連接性を主張しない。§20 の O 加群射とその同型性が追加の証明を与える。
- アフィン切断の同型だけで導来圏・dg 圏・降下模型の同値を主張しない。

## 20. 構造層加群としてのアフィン比較

- 係数環層を自分自身への左作用で加群層とし、構造層へスカラー制限する。
- H の定数切断は大域切断への R 線形写像を与える。
- R 線形性は基礎環上の二つの作用の一致から証明する。
- tilde と大域切断の随伴を用いて tilde H からこの O 加群層への射を作る。
- この射が標準切断にどう作用するかを、随伴の余単位との計算式で示す。
- 基本開上では純テンソル上の式を用い、既存の環層化の比較射と一致させる。
- 既存の基本開上の同型判定と開基による層の同型判定で、O 加群層の同型を得る。
- tilde H の準連接性をこの同型で移送する。
- 上記の標準構造射 Spec R 上の各比較・準連接性は Lean で実装し対象ビルド済み。
- これは KST D4・T1 の係数環層の準連接性への入力であり、T1 のコンパクト生成は含まない。
- 一般の A → R の底変換は §21 で証明済み。一般の X の開部分への係数環層の制限との両立は §22 の別定理で証明済み。

## 21. 一般の基礎環からのアフィン底変換

- A → R → S を可換環の塔、H を任意の結合 A 代数とする。
- H の非可換性を保ったまま、S ⊗_R (R ⊗_A H) と S ⊗_A H を比較する。
- Mathlib のテンソル結合子の逆と右単位の同型を合成し、S 代数の同型を構成する。
- H に R 作用を要求する結合子を誤って H ⊗_A R 側へ直接適用しない。
- 純テンソル s ⊗ (r ⊗ h) は (r • s) ⊗ h に送られることを記録する。
- 因子の交換と右側の代数構造を用い、(H ⊗_A R) ⊗_R S と H ⊗_A S を比較する。
- S = O_SpecR(U) へ適用する際、切断の A 作用と R 作用の塔の両立を明示する。
- 制限写像との自然性、前層の自然同型、層化との比較を順に示す。
- 原典の接続は KST D4、Toën Derived Azumaya §3.2。平坦性はこの環の底変換には不要。
- 二つの向きの底変換の環同型と純テンソル上の計算式、R 代数準同型への自然性を証明済み。
- 各開のテンソル前層の環同型を自然同型として束ね、構造層からの単位との両立を証明済み。
- 環の圏で層化し、環層の同型・比較射との可換式・構造層射との可換式を証明済み。
- 基本開およびアフィン全体で、一段のテンソル前層から係数環層への比較が環同型になる。
- 構造層射を保つ一般の係数環層の射から正則 O 加群の射を構成した。
- 係数環層の同型に対し、この正則加群の射も同型になることを証明済み。
- 正則 O 加群と tilde (H ⊗_A R) の同型を構成し、準連接性を証明済み。
- affineBaseMap は実際の Spec R → Spec A の構造射から得る globalBaseMap と一致する。
- coefficientSheafOfMorphism による実際の構成にもアフィン準連接性を適用済み。
- 一般の X の開部分への制限との比較は §22、アフィン開と Spec Γ(U) の同型に沿う輸送は §23 で証明済み。導来・dg 圏の比較は未証明。

## 22. 開部分への制限と係数環層の構成

- 開埋め込みに伴う開集合の像の関手は連続かつ余連続なサイトの関手である。
- 連続性は Mathlib の開埋め込みの定理、余連続性は開像と逆像の随伴と被覆保存から証明する。
- この二つの性質による層化との自然同型を用い、制限と環の層化が可換であることを示す。
- 比較射と層化の単位の可換式も明示する。
- U ⊆ X への基礎環写像は、a : A → Γ(X,⊤) を Γ(U,⊤) へ制限したものとする。
- U の任意の開 V 上で、その A 作用は X の像の開に指定した A 作用と一致する。
- この代数構造の等式でテンソルの環を移送し、前層の自然同型を作る。
- 切断の型は一致してもスカラー作用を定義的に同一とせず、移送と純テンソルの計算式を記録する。
- 前層の同型と層化・制限の同型を合成し、直接構成と制限による係数環層を比較する。
- 構造層射との両立を示した後、正則 O 加群の比較と一般の X 上の準連接性へ進む。
- 原典は KST D4、Toën Derived Azumaya §3.2。導来降下との交換はこの層の比較からは結論しない。
- 開埋め込みの開像の関手の連続性・余連続性と、制限と層化の自然同型・単位との可換式を証明済み。
- 開部分への基礎環写像と実際の構造射の合成の両立、各開の切断の代数構造の一致を証明済み。
- 代数構造の等式の移送を環の束で扱い、純テンソルを保つことを確認した。
- 直接構成した係数テンソル前層と大域前層の制限の自然同型・単位との可換式を証明済み。
- 環層の開制限同型、層化前の比較射との可換式、構造層射との可換式を証明済み。
- 一般の CoefficientSheaf の開制限と、その正則 O 加群の開制限との標準同型を構成済み。
- 具体的な係数環層の正則 O 加群も、直接構成と Mathlib の開制限関手による制限とで同型になる。
- 実際の構造射からの coefficientSheafOfMorphism にも、環層・正則 O 加群の両方の制限同型を構成済み。
- §22 の制限比較だけでは一般の X 上の準連接性は結論しない。§23 のアフィン同型による輸送と局所判定の追加証明を用いる。

## 23. 開埋め込み・アフィン同型に沿う輸送

- 文字どおりの開部分への制限に続き、任意の開埋め込み f : X → Y に沿う係数比較を構成する。
- X 上の基礎環写像は f.appTop と a : A → Γ(Y,⊤) の合成とする。
- 各開 V で appIso V の逆が基礎環の作用を保つことを、appLE_appIso_inv から証明する。
- 切断環の同型を A 代数の同型へ束ね、H とのテンソルを取る。
- appIso_inv_naturality によりテンソル前層の自然同型を構成し、構造層射との可換性を確認する。
- 開埋め込みのサイトの層化比較で環層へ移す。
- Mathlib の構造層加群の restrictFunctor と正則加群を同定する。
- スキーム同型にも適用できるので、アフィン X と Spec Γ(X,⊤) の間で準連接性を輸送する。
- その後、開被覆による準連接性の局所判定を用いて一般の X の係数環層を扱う。
- ここでは層の準連接性までを扱い、D_qc のアフィン同値・導来降下・compact 性は別の工程とする。
- 原典は KST D4、Bondal–van den Bergh Thm 3.1.1、Toën Derived Azumaya §3.2。
- appIso の逆による構造層射、基礎環の作用との両立、切断の A 代数同型を実装・証明済み。
- 任意の開埋め込みに対する係数前層の自然同型と単位との可換式を証明済み。
- 環層の比較、層化前の比較射との可換式、構造層射との可換式を証明済み。
- 一般の係数環層の開埋め込みに沿う制限を構成し、正則 O 加群の制限同型を証明済み。
- 終域の正則加群の準連接性から始域の直接構成の準連接性を得る補題を証明済み。
- X.toSpecΓ の大域切断の計算で基礎環作用の引き戻しが元に戻ることを証明済み。
- これにより任意のアフィンスキーム X 上の正則係数加群の準連接性を証明済み。
- Mathlib の overFunctorEquiv を使い、開部分上の制限の準連接性からスライスサイト上の制限の準連接性を得た。
- サイト同値の Over.post の連続性は、被覆保存と平坦性から明示的に証明する。
- 開被覆による準連接性判定は IsQuasicoherent.of_coversTop に接続して証明済み。
- 全アフィン開の被覆に適用し、任意のスキーム上の H_X の正則 O 加群の準連接性を証明済み。
- 実際の構造射から作る coefficientSheafOfMorphism についても同じ準連接性を証明済み。
- 係数環層の準連接性だけで、自由関手が全 D_qc を生成することや T1′ を主張しない。

## 24. アフィン係数加群圏と大域切断

- 係数環層 B の加群層で、O_X 加群へ忘れたものが準連接な対象の充満部分圏 QCoh(B) を定義する。
- D_qc のコホモロジー条件とこの層レベルの対象条件を区別する。
- Spec R と R 代数 H について、大域定数切断 H → Γ(H_X,⊤) が環の同型であることを示す。
- 正則 O 加群の tilde H との同型と tilde の大域切断の同型を使い、指定された定数切断の全単射性を得る。
- 係数加群層の大域切断を取り、この H の作用へスカラー制限して ModuleCat H への関手を構成する。
- R へ忘れた大域切断と、係数を O_X へ忘れてから大域切断を取るものを自然同型で比較する。
- Mathlib の tildeEquiv を用いて、QCoh(B) 上での大域切断の忠実性・同型の反映へ接続する。
- 完全充満性と本質的全射性には H_X の作用の再構成が必要であり、忘却関手の保存性だけからは結論しない。
- その作用の再構成、アフィン dg 加群圏との導来比較、有限被覆の導来降下は後続の証明として残す。
- 原典は KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën Derived Azumaya §3.2。
- QCoh(B) とその包含・通常の準連接 O 加群への忘却を実装済み。係数忘却の忠実性・同型の反映も移送済み。
- 指定された H の定数切断から大域切断環への環同型を証明済み。
- 全係数加群層と準連接係数加群層の両方で H 加群としての大域切断関手を構成済み。
- R へ忘却した関手と通常の O 加群の大域切断の自然同型を証明済み。
- tildeEquiv の逆との比較から、QCoh(B) 上の大域切断が忠実かつ同型を反映することを証明済み。
- 準連接な始域からの O 加群層の射が大域切断で決まる補題を、tilde 随伴の余単位から証明済み。
- H の定数作用を基礎 O 加群層の自己準同型とし、H からその自己準同型環への環準同型を構成済み。
- この作用の係数加群層の射についての自然性を証明済み。
- 大域切断上で H 線形な O 加群層の射が定数 H 作用と層全体で可換になることを証明済み。
- 全 H_X 切断の作用への線形性を局所的なテンソル持ち上げで示す段階、充満性、本質的全射性は残る。

## 25. 層の複体の dg 圏と acyclic の商

- 正本 §13 決定11の dg 増強の始域は、全 H_X 加群層の非有界コチェイン複体とする。
- 既存 DifferentialGraded.Complex は可換環と同じ宇宙の加群複体専用なので、層の複体をその対象と定義的に同一視しない。
- Mathlib の linearHomComplex は任意の線形加法圏の複体に使えるので、実際の層複体の Hom 複体に採用する。
- dg 圏の係数環は Hom の宇宙に合わせた ULift ℤ とし、通常の整数による加法的作用をスカラー制限で持ち上げる。
- この宇宙の調整は係数環層 H_X 自体の変更ではない。
- 既存 dg 商は対象型の Small 条件を係数環の宇宙に対して要求する。全層複体の対象は層の Hom より一段大きいので、ULiftHom によって Hom も対象の宇宙まで持ち上げる。
- ULiftHom 上の複体と元の層複体との圏同値を示し、acyclic と準連接コホモロジーはその比較で実際の層複体の条件から定める。
- これにより全層複体を不当に小さい型と仮定せず、既存 dg 商の Small 条件を満たす。
- dg 合成は Mathlib の Cochain.comp と δ_comp を用い、既存の tensorLift・単位複体・符号つき交換を再利用する。
- 豊穣順の合成は f ⊗ g を (-1)^(deg f deg g) g∘f へ送る既存規約と一致させる。
- 閉次数零の圏を実際の層複体の圏と比較し、H⁰ を Mathlib のホモトピー圏と比較する。
- acyclic は層複体の実際の全コホモロジーが零であることにより指定する。
- 既存の Drinfeld dg 商にこの対象集合を渡し、商の H⁰ と層複体の導来局所化との比較を別途証明する。
- D_qc は忘却後のコホモロジーの準連接性による充満部分圏として保つ。
- 単に dg 商の型を作っただけで Mathlib の DerivedCategory との同値を主張しない。
- 一般の線形加法圏の複体について写像複体・dg 合成とその三法則を Lean で証明済み。
- 閉次数零と通常の chain map の比較は単位・合成を保つ圏同値として証明済み。
- dg 境界関係と通常の鎖ホモトピーの一致、および H⁰ と通常のホモトピー圏の同値を証明済み。
- ULiftHom の加法的構造・持ち上げた整数環上の線形構造と、元の層複体との圏同値を構成済み。
- 層複体の dg 圏の Z⁰・H⁰ から元の層複体の圏・ホモトピー圏への同値を構成済み。
- 元の層複体の acyclic 条件が全コホモロジーの零性と一致することを証明済み。
- 既存 Drinfeld 商に acyclic の集合を渡し、標準 dg 関手と指定収縮を構成済み。
- acyclic 対象の像の恒等射が境界となり、商の H⁰ で零対象になることを証明済み。
- 商の対象に準連接コホモロジーの条件を課した充満 dg 部分模型 DqcDGModel を構成済み。
- その対象条件と、元の複体の Mathlib 導来像についての既存 Dqc の対象条件の同値を証明済み。
- 対象条件の一致だけでは、商から Mathlib の導来圏への関手・完全充満性・圏同値はまだ得ていない。
- その比較では既存 dg 商の定理の前提、とくに K-flat 条件が現れる箇所を照合し、未証明の前提を追加仮定として済ませない。
- 原典は KST D4・§13 決定11、Drinfeld の dg 商、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。

## 26. §10-7 の再照合：平坦分解を経る導来 dg 商の採用設計

### 原典の条件と現実装の限界

- 原典：[Drinfeld, DG quotients of DG categories](https://arxiv.org/abs/math/0210114)、Thm 3.4、§3.5、Lemma 13.5。
- Thm 3.4 は、殺す対象へ入る全 Hom、または殺す対象から出る全 Hom の K-flat 性を要求する。
- 既存 `DGQuotient.localKFlat` もこの二つの片側条件の選言であり、対象ごとの選言ではない。
- `localPerfectQuotientEquivalence` はこの条件を引数に取り、条件自体を証明する定理ではない。
- 現在の基礎環は宇宙を持ち上げた整数環。宇宙の調整から Hom の K-flat 性は導けない。
- 全係数加群層の Hom 複体に対する片側 K-flat 性は現状では未証明。
- acyclic 対象を商で収縮させたことだけでは Verdier 局所化との同値は証明できていない。
- 未分解の層複体の path 商を最終模型としては使わない。現 `DerivedDG` は §27–28 の平坦分解後の商。
- `mem_dqcDGObjects_iff` は対象条件の一致。関手の完全充満性を含まない。

### 変更案と実装前の証明方針

- §13 決定11の対象となる導来圏、係数環層、準連接コホモロジー条件は維持する。
- 採用された dg 増強の構成順序は、以下の平坦分解を先行させるものとする。
- 全層複体 dg 圏 C に対し、対象を保つ半自由 dg 圏 C̃ と準同値 C̃ → C を構成する。
- Lemma 13.5 の段階的生成元添加を形式化し、Hom 上の全射準同型と準同型性を証明する。
- 半自由フィルトレーションから Hom 複体の K-flat 性を証明する。次数ごとの自由性だけで非有界 K-flat 性を済ませない。
- C̃ の中で、像が acyclic である対象を充満部分圏 Ñ として取る。
- C̃/Ñ を既存の明示的 path 商で構成し、Thm 3.4 の前提を証明して適用する。
- 前三角化および準同値による移送を経て H⁰ と Mathlib 導来圏の同値を証明する。
- その後、準連接コホモロジー条件へ制限して Dqc の dg 増強を得る。
- 平坦分解の存在・K-flat 性・導来比較を構造体の未証明フィールドや追加公理にはしない。
- 係数環 H の平坦性は追加しない。L4e の平坦性仮定と dg 基礎環上の条件を混同しない。
- 既存の複体の K-flat 分解と dg 圏の半自由分解は別構成であり、前者の項別適用で合成の整合性を済ませない。

### 影響と現在地

- `DifferentialGraded/` は読み取り専用を維持し、一般定理の入口は所有ディレクトリに置く。
- 既存 path 商・指定収縮を再利用し、平坦分解後の acyclic の零性を証明する。
- `DerivedDG`・`DqcDGModel` の平坦分解後の構成への移行は完了。導来圏との H⁰ 比較は保留。
- L4a の完了、L4b–e の完了は主張しない。
- 設計変更の採用により判断待ちは解消。正本や他レーンのファイルは変更しない。

## 27. 採用された Lemma 13.5 の構成と証明方針（実装前記録）

- 2026-10-18、ユーザーが §26 を採用。以下の方針で承認待ちを終えて実装へ進む。
- 正本 §13-11 の層レベルの定義は維持する。正本自体は編集しない。
- 配置は `KST/DerivedGeometry/DGResolution/`、namespace は `SerrePositivity.KST.DerivedGeometry.DGResolution`。
- 可換環 A と任意の dg 圏 D をパラメータとし、層や K 理論に依存しない。
- 直和の宇宙には `Small.{u} D` を明示する。層への適用では既存の宇宙調整を使う。

### 構成の文言

- Drinfeld Lemma 13.5：対象を固定した半自由 dg 圏からの増大関手を構成し、各 Hom で全射準同型を得る。
- 初期段階は離散 dg 圏。全 Hom の閉元を球生成元として添加する。
- 任意の斉次元の持ち上げには、その微分の閉元を先に持ち上げ、原始元を次の段階で添加する。
- 各後続段階で、源の閉元 z と標的の原始元 b（像 z = db）すべてに対し dt = z、像 t = b となる生成元 t を添加する。
- 生成元の微分は前段階に属し、有限語に Leibniz 則で延長する。
- 列の余極限を C̃ とする。閉元の持ち上げと核の境界化から Hom の準同型性を証明する。
- 同じ充填を微分の持ち上げに適用し、各次数の全射性も証明する。

### K-flat 性と移送の証明方針

- 初期の球生成元は自由加群の shift。有限語の tensor と直和は K-flat。
- 一段の生成元添加では、新生成元の語長フィルトレーションを使う。追加微分は語長を下げる。
- 各随伴次数は前段階の Hom と球生成元の tensor の直和。
- 次数別分裂の短完全列を用いて有限フィルトレーション段階へ帰納する。
- 語長と生成元添加段階の二つの逐次余極限に、加群圏の完全な filtered colimit を使う。
- よって任意の非有界 acyclic 複体との tensor が acyclic。次数ごとの自由性だけを根拠にしない。
- 準同値による H⁰ の同値、前三角化との両立を証明し終えるまで Dqc・Perf の増強への適用は行わない。
- 既存 path 商には証明した `DGQuotient.localKFlat` を渡す。比較定理や分解の存在を未証明フィールドにしない。

### 既存の証明済み部品の利用

- 読み取り調査で `DifferentialGraded/Resolution/` に自由 dg 圏、境界生成元添加、逐次余極限の構成を確認した。
- `CellSequence.candidateHom_kFlat` は語長フィルトレーションと逐次余極限に基づく既存の証明を使う。
- `CellCategory.augmentation_quasiEquivalence` は具体的増大関手について証明済み。
- これらの証明を再利用し、所有ディレクトリで一般定理と各次数全射性・商への供給を整備する。
- 既存構造体 `KFlatDGResolution` のフィールドを外部仮定として受け取る入口にはしない。
- 元の Hom の平坦性・有界性は追加しない。`DifferentialGraded/` は編集しない。

### 実装と検証の現在地

- `Filtration`：任意の生成元添加の有限語長・全語長・全添加段階の K-flat 性を証明した。
- `Construction`：具体的分解の対象、増大関手、準同値、H⁰ の圏同値、任意集合に対する localKFlat を公開した。
- `Surjectivity`：微分の閉元持ち上げと一段の原始元添加から増大関手の各次数全射性を証明した。
- `Pretriangulation`：任意の dg 準同値について有限 cell の三角閉包 tria の同値を構成した。
- `PretriangulationTriangles`：包含正方形、shift、区別三角形、随伴の単位と shift の両立を証明した。
- `Quotient`：分解後の逆像部分圏の path 商を構成し、既存の完備化前・後の商比較へ証明済み localKFlat を渡した。
- 元の圏の Verdier 商へ戻す正方形は §28 で実装済み。層の acyclic 商自体の H⁰ の導来圏比較は未実装。
- 最新の対象ビルドと公理監査の結果は §3・§28 を参照。

## 28. 分解前後の指定部分圏と Verdier 商の移送（実装前記録）

- §10-7 の導来比較に先立ち、増大準同値の tria 同値が指定対象集合の三角閉包を対応させることを証明する。
- 順向き：指定代表加群の像が指定代表加群に同型であり、逆像部分圏は三角的なので最小性を使う。
- 逆向き：増大関手は対象ラベルを保つため、各指定対象は指定持ち上げを持つ。導来随伴の単位で代表加群を戻す。
- この二方向と単位同型により、指定閉包の membership の同値を証明する。
- `inverseImage_trW_iff` で三角局所化の弱同値を対応させ、既存の局所化の普遍性から商の移送を得る。
- 元の Hom の平坦性を加えず、分解後の商の三角比較を元の指定 Verdier 商へ接続する。
- 層への特殊化は一般の移送の証明後に行う。Mathlib 導来圏の局所化の universal property と照合する。

### 実装と残りの接続

- `SupportTransport`：指定対象の三角閉包が増大準同値の前三角化延長と対応することを証明済み。
- `VerdierTransport`：trW の逆像の一致、実際の局所化の可換正方形、分解前後の Verdier 商の三角同値を証明済み。
- `quotientToOriginalVerdierEquivalence`：平坦分解後の path 商の tria と元の指定 Verdier 商の三角同値。
- `SheafDerivedDG`：ResolvedComplexes → Complexes と、ResolvedComplexes → DerivedDG の屋根へ変更済み。
- `DqcDGModel`：商の元の対象を増大関手で戻し、実際の層コホモロジーの準連接性を判定する。
- `ResolvedSheafComparison`：分解の H⁰ と実際の層複体のホモトピー圏の同値、商の tria の三角比較を実装済み。
- 残る比較は、複体 dg 圏とその商の前三角化の代表可能性、および Mathlib の導来局所化との同定。
- tria の同値を商自体の H⁰ の同値と同一視しない。L4a 全体の完了は主張しない。
- 対象ビルドと644宣言の公理監査に成功。標準3公理のみ、KTheory import なし。

## 29. Lemma 13.5 の半自由な段階表示の明示（実装前記録）

- 現在の分解は具体的な閉元被覆・生成元添加列から構成済み。今回はその段階表示を一般 API として明示する。
- 生成元添加の Hom は、前段階の Hom と球生成元を交互に並べた有限語の直和。
- 空語への射影は内部微分についての chain map だが、追加微分後には一般に chain map ではない。
- この空語射影を次数ごとにのみ使い、前段階の包含が次数別に分裂単射であることを証明する。
- 逐次列の全遷移射を単射とし、filtered colimit の完全性から各有限段階の極限への包含も単射とする。
- 具体的な余極限の元の有限段表示と合わせて、段階列の網羅性を示す。
- 各後続段階の生成元 t について、dt は前段階の指定閉元、増大像は指定原始元であることを明示する。
- 一段の添加からの dg 関手と、前段階の dg 関手および指定境界を持つ生成元の像の組の全単射を構成する。延長・制限の往復を証明し、自由添加の普遍性を公開する。
- 初期段階も、閉元ごとの球を生成辺とする自由 dg 圏であることを普遍性で明示する。球の直和からの射を各生成元の閉じた像と対応させ、初期自由圏の普遍性と合成する。
- 「次数別に分裂」を複体の分裂と混同せず、K-flat 性の証明は §27 のフィルトレーションのものを維持する。
- 未証明の半自由性・分解の存在を構造体へ入れない。一般の可換環・dg 圏に対する所有ディレクトリの定理とする。

### 現在地

- `CellEmbedding`：空語射影による次数別分裂単射と、添加した複体への包含の単射性を証明済み。
- `StagePresentation`：段階ごとの生成元、指定微分、増大像を公開し、それらが極限でも維持されることを証明済み。
- 全段階間の遷移射と各段階から極限への包含が単射であり、斉次元・閉元が有限段階から来ることを証明済み。
- `CellUniversal`：添加した dg 圏からの関手と、前段階の関手および指定原始元のデータが全単射に対応する。順写像が実際の制限・評価であることも証明済み。
- `InitialPresentation`：初期の自由 dg 圏からの関手が、対象写像と球生成元の閉じた像で分類されることを証明済み。
- 任意の対象集合に対する商の供給は §27–28 の実装をそのまま維持する。K-flat 性を次数別分裂だけから再定義しない。
- 対象ビルドと698宣言の公理監査に成功。標準3公理のみ、KTheory import なし。
- 設計上の判断待ち・所有 import 閉包の破損はない。商自体の H⁰ と Mathlib 導来圏の比較は未完了。

## 主要宣言の表

| 宣言・接続点 | 配置 | 状態 |
| --- | --- | --- |
| `CoefficientSheaf`・`Modules`・`forget` | DerivedGeometry/CoefficientSheaf | 実装・対象ビルド済み |
| `underlyingCohomology`・`hasQuasicoherentCohomology`・`Dqc` | DerivedGeometry/CoefficientSheaf | 実装・対象ビルド済み |
| `hasQuasicoherentCohomology_closedUnderIso`・`dqcInclusion` | DerivedGeometry/CoefficientSheaf | 実装・対象ビルド済み |
| `FiniteAffineCoverOf`・`finiteAffineCover` | DerivedGeometry/FiniteAffineCover | 実装・対象ビルド済み |
| `affineIntersectionCover` | DerivedGeometry/FiniteAffineCover | 実装・対象ビルド済み |
| `forget_faithful`・`forget_reflectsIsomorphisms` | DerivedGeometry/CoefficientForget | 実装・対象ビルド済み |
| `preservesColimitsOfShape_of_reflective` | DerivedGeometry/ReflectiveColimits | 実装・対象ビルド済み |
| `toSheaf_preservesColimits`・`forget_preservesFiniteLimits`・`forget_preservesColimits` | DerivedGeometry/CoefficientExact | 実装・対象ビルド済み |
| `forget_preservesFiniteColimits` | DerivedGeometry/CoefficientExact | 実装・対象ビルド済み |
| `free`・`freeForgetAdjunction` | DerivedGeometry/CoefficientAdjunction | 実装・対象ビルド済み |
| `derivedForget`・`derivedForgetHomologyIso` | DerivedGeometry/DerivedForget | 実装・対象ビルド済み |
| `derivedForget_reflectsIsomorphisms` | DerivedGeometry/DerivedForget | 実装・対象ビルド済み |
| `DqcO`・`hasQuasicoherentCohomology_iff`・`dqcForget` | DerivedGeometry/DqcForget | 実装・対象ビルド済み |
| `dqcForget_reflectsIsomorphisms` | DerivedGeometry/DqcForget | 実装・対象ビルド済み |
| `globalBaseMap`・`sectionBaseMap`・`sectionRestriction` | DerivedGeometry/BaseSections | 実装・対象ビルド済み |
| `coefficientTensorPresheaf`・`coefficientTensorUnit` | DerivedGeometry/CoefficientTensorPresheaf | 実装・対象ビルド済み |
| `coefficientTensorConstant`・`coefficientTensorUnit_commutes` | DerivedGeometry/CoefficientTensorAction | 実装・対象ビルド済み |
| `tensorCoefficientSheaf`・`coefficientSheafOfMorphism` | DerivedGeometry/TensorCoefficientSheaf | 実装・対象ビルド済み |
| `tensorCoefficientConstant_comp_algebraMap` | DerivedGeometry/TensorCoefficientAction | 実装・対象ビルド済み |
| `tensorCoefficientSheaf_structureMap_commutes`・`tensorCoefficientSectionAlgebra` | DerivedGeometry/TensorCoefficientAction | 実装・対象ビルド済み |
| `tensorCoefficientSelfIso` | DerivedGeometry/TensorCoefficientUnit | 実装・対象ビルド済み |
| `sectionBaseMap_spec`・`sectionAlgebra_spec` | DerivedGeometry/AffineTensorSections | 実装・対象ビルド済み |
| `affineBasicTensorSectionsEquiv`・`affineBasicTensorSectionsEquiv_tmul` | DerivedGeometry/AffineTensorSections | 実装・対象ビルド済み |
| `affineTensorSectionMap_naturality`・`affineTensorToTilde_basic_isIso` | DerivedGeometry/AffineTensorComparison | 実装・対象ビルド済み |
| `locallyInjective_of_basis`・`locallySurjective_of_basis` | DerivedGeometry/BasisLocalComparison | 実装・対象ビルド済み |
| `affineTensorSheafIso`・`toSheafify_affineTensorSheafIso` | DerivedGeometry/AffineTensorSheaf | 実装・対象ビルド済み |
| `affineCoefficientAdditiveIso` | DerivedGeometry/AffineCoefficientComparison | 実装・対象ビルド済み |
| `preservesSheafification_of_forget` | DerivedGeometry/ForgetSheafification | 実装・対象ビルド済み |
| `affineCoefficientSheafAdditiveIso`・`affineCoefficientSheafAdditiveIso_fac` | DerivedGeometry/AffineCoefficientSheaf | 実装・対象ビルド済み |
| `affineCoefficientComparison_basic_isIso`・`affineCoefficientComparison_top_isIso` | DerivedGeometry/AffineCoefficientSections | 実装・対象ビルド済み |
| `CoefficientSheaf.regular`・`affineCoefficientConstantLinear` | DerivedGeometry/AffineCoefficientModule | 実装・対象ビルド済み |
| `affineCoefficientModuleMap`・`toOpen_affineCoefficientModuleMap`・`affineCoefficientModuleMap_tmul` | DerivedGeometry/AffineCoefficientModule | 実装・対象ビルド済み |
| `affineCoefficientModuleMap_fac`・`affineCoefficientModuleMap_isIso` | DerivedGeometry/AffineCoefficientQuasicoherent | 実装・対象ビルド済み |
| `affineCoefficientModuleIso`・`affineCoefficientRegular_isQuasicoherent` | DerivedGeometry/AffineCoefficientQuasicoherent | 実装・対象ビルド済み |
| `tensorBaseChangeCancel`・`tensorBaseChangeRight`・`tensorBaseChangeRight_naturality` | DerivedGeometry/TensorBaseChange | 実装・対象ビルド済み |
| `affineBaseMap`・`globalBaseMap_spec`・`affineBaseSectionScalarTower` | DerivedGeometry/AffineBaseChangeSections | 実装・対象ビルド済み |
| `affineCoefficientBaseChangeIso`・`affineCoefficientBaseChangeIso_unit` | DerivedGeometry/AffineBaseChangeSections | 実装・対象ビルド済み |
| `affineCoefficientBaseChangeSheafIso`・`affineCoefficientBaseChangeSheafIso_structureMap` | DerivedGeometry/AffineBaseChangeSheaf | 実装・対象ビルド済み |
| `affineBaseCoefficientComparison_basic_isIso`・`affineBaseCoefficientComparison_top_isIso` | DerivedGeometry/AffineBaseChangeSheaf | 実装・対象ビルド済み |
| `CoefficientSheaf.regularMap`・`regularMap_isIso` | DerivedGeometry/CoefficientRegularMap | 実装・対象ビルド済み |
| `affineBaseCoefficientModuleIso`・`affineBaseCoefficientRegular_isQuasicoherent` | DerivedGeometry/AffineBaseChangeQuasicoherent | 実装・対象ビルド済み |
| `coefficientSheafOfSpecMap_regular_isQuasicoherent` | DerivedGeometry/AffineBaseChangeQuasicoherent | 実装・対象ビルド済み |
| `openEmbedding_isCocontinuous`・`openSheafificationIso`・`openSheafificationIso_fac` | DerivedGeometry/OpenSheafification | 実装・対象ビルド済み |
| `restrictedBaseMap`・`globalBaseMap_restrict`・`sectionAlgebra_restrict` | DerivedGeometry/OpenBaseSections | 実装・対象ビルド済み |
| `tensorRingObject`・`tensorRingPure_cast`・`tensorRingObject_hom_ext` | DerivedGeometry/TensorScalarTransport | 実装・対象ビルド済み |
| `openTensorPresheafIso`・`openTensorPresheafIso_unit` | DerivedGeometry/OpenTensorPresheaf | 実装・対象ビルド済み |
| `CoefficientSheaf.restrict` | DerivedGeometry/CoefficientRestriction | 実装・対象ビルド済み |
| `openTensorSheafIso`・`openTensorSheafIso_structureMap` | DerivedGeometry/OpenTensorSheaf | 実装・対象ビルド済み |
| `coefficientSheafOfMorphism_restrictIso` | DerivedGeometry/OpenTensorSheaf | 実装・対象ビルド済み |
| `CoefficientSheaf.regularRestrictIso` | DerivedGeometry/CoefficientRegularRestriction | 実装・対象ビルド済み |
| `openTensorRegularIso`・`coefficientSheafOfMorphism_regularRestrictIso` | DerivedGeometry/OpenTensorRegular | 実装・対象ビルド済み |
| `openImmersionStructureMap`・`appIso_inv_comp_sectionBaseMap`・`openImmersionSectionAlgEquiv` | DerivedGeometry/OpenImmersionBase | 実装・対象ビルド済み |
| `openImmersionTensorPresheafIso`・`openImmersionTensorPresheafIso_unit` | DerivedGeometry/OpenImmersionTensorPresheaf | 実装・対象ビルド済み |
| `CoefficientSheaf.restrictAlong` | DerivedGeometry/CoefficientOpenImmersion | 実装・対象ビルド済み |
| `openImmersionTensorSheafIso`・`openImmersionTensorSheafIso_structureMap` | DerivedGeometry/OpenImmersionTensorSheaf | 実装・対象ビルド済み |
| `regularRestrictAlongIso`・`openImmersionTensorRegularIso` | DerivedGeometry/OpenImmersionTensorRegular | 実装・対象ビルド済み |
| `pullbackBaseMap_toSpecΓ`・`affineSchemeCoefficientRegular_isQuasicoherent` | DerivedGeometry/AffineSchemeCoefficient | 実装・対象ビルド済み |
| `moduleOver_isQuasicoherent_of_restrict`・`module_isQuasicoherent_of_openCover` | DerivedGeometry/QuasicoherentOpenCriterion | 実装・対象ビルド済み |
| `tensorCoefficientRegular_isQuasicoherent`・`coefficientSheafOfMorphism_regular_isQuasicoherent` | DerivedGeometry/CoefficientQuasicoherent | 実装・対象ビルド済み |
| `hasQuasicoherentUnderlying`・`QCoh`・`qcohInclusion`・`qcohForget` | DerivedGeometry/QuasicoherentCoefficient | 実装・対象ビルド済み |
| `qcohForget_faithful`・`qcohForget_reflectsIsomorphisms` | DerivedGeometry/QuasicoherentCoefficient | 実装・対象ビルド済み |
| `affineCoefficientConstant_top_isIso`・`affineCoefficientGlobalIso` | DerivedGeometry/AffineCoefficientGlobalRing | 実装・対象ビルド済み |
| `affineCoefficientΓ`・`affineCoefficientΓForgetIso`・`affineQcohΓ`・`affineQcohΓForgetIso` | DerivedGeometry/AffineCoefficientSectionsFunctor | 実装・対象ビルド済み |
| `affineUnderlyingHom_ext`・`affineQcohΓ_faithful`・`affineQcohΓ_reflectsIsomorphisms` | DerivedGeometry/AffineQuasicoherentSections | 実装・対象ビルド済み |
| `coefficientConstantAction`・`coefficientConstantActionRingHom`・`coefficientConstantActionNat` | DerivedGeometry/CoefficientConstantAction | 実装・対象ビルド済み |
| `affineUnderlyingHom_commutesConstant` | DerivedGeometry/AffineQuasicoherentActions | 実装・対象ビルド済み |
| `LinearComplex.mappingComplex`・`composition`・`forwardComposition` | DerivedGeometry/LinearComplexMapping | 実装・対象ビルド済み |
| `LinearComplex.enrichment` | DerivedGeometry/LinearComplexEnrichment | 実装・対象ビルド済み |
| `LinearComplex.closedToComplex_isEquivalence` | DerivedGeometry/LinearComplexClosed | 実装・対象ビルド済み |
| `LinearComplex.boundary_iff`・`homotopyComparison_isEquivalence` | DerivedGeometry/LinearComplexHomotopy | 実装・対象ビルド済み |
| `CoefficientDGBase`・`LiftedModules`・`complexLiftEquivalence`・`complexesDGCategory` | DerivedGeometry/LiftedCoefficientComplex | 実装・対象ビルド済み |
| `closedComplexEquivalence`・`homotopyComplexEquivalence` | DerivedGeometry/CoefficientComplexComparison | 実装・対象ビルド済み |
| `acyclicComplexes`・`mem_acyclicComplexes_iff` | DerivedGeometry/SheafDerivedDG | 実装・対象ビルド済み |
| `DerivedDG`・`derivedDGProjection`・`derivedDGContractedProjection`・`derivedDG_acyclic_isZero` | DerivedGeometry/SheafDerivedDG | 実装・対象ビルド済み |
| `DqcDGModel`・`dqcDGModelInclusion`・`mem_dqcDGObjects_iff` | DerivedGeometry/DqcDGModel | 実装・対象ビルド済み |
| `DGResolution.finiteLength_kFlat`・`attachment_kFlat`・`stage_kFlat`・`limitHom_kFlat` | DGResolution/Filtration | 実装・対象ビルド済み |
| `DGResolution.Objects`・`augmentation_quasiEquivalence`・`augmentation_homotopy_isEquivalence` | DGResolution/Construction | 実装・対象ビルド済み |
| `DGResolution.augmentation_surjective`・`augmentation_degree_epi` | DGResolution/Surjectivity | 実装・対象ビルド済み |
| `DGResolution.triaEquivalence`・`triaEquivalenceIsTriangulated` | DGResolution/Pretriangulation・PretriangulationTriangles | 実装・対象ビルド済み |
| `DGResolution.localKFlat`・`quotientTriaEquivalence`・`perfectQuotientEquivalence` | DGResolution/Construction・Quotient | 実装・対象ビルド済み |
| `DGResolution.attachment_degree_splitMono`・`attachment_mono` | DGResolution/CellEmbedding | 実装・対象ビルド済み |
| `DGResolution.stageGenerator_differential`・`limitGenerator_differential`・`limitGenerator_augmentation` | DGResolution/StagePresentation | 実装・対象ビルド済み |
| `DGResolution.stageInclusion_degree_mono`・`homogeneous_finiteStage`・`cycle_finiteStage` | DGResolution/StagePresentation | 実装・対象ビルド済み |
| `DGResolution.cellFunctorEquiv`・`cellFunctorEquiv_apply` | DGResolution/CellUniversal | 実装・対象ビルド済み |
| `DGResolution.cycleCoverHomEquiv`・`initialFunctorEquiv` | DGResolution/InitialPresentation | 実装・対象ビルド済み |
| `DGResolution.augmentation_triaImage_iff`・`augmentation_trW_eq` | DGResolution/SupportTransport・VerdierTransport | 実装・対象ビルド済み |
| `DGResolution.verdierSquare`・`quotientToOriginalVerdierIsTriangulated` | DGResolution/VerdierTransport | 実装・対象ビルド済み |
| `ResolvedComplexes`・`resolvedAcyclicComplexes`・`resolvedAugmentation_quasiEquivalence` | DerivedGeometry/SheafDerivedDG | 実装・対象ビルド済み |
| `resolvedHomotopyComplexEquivalence`・`derivedDGTriaEquivalenceIsTriangulated` | DerivedGeometry/ResolvedSheafComparison | 実装・対象ビルド済み |
| dg 商自体の H⁰ と Mathlib の導来圏との同値 | DerivedGeometry/ | 前三角化の代表可能性と導来局所化の同定は未実装 |
| 層の降下 | DerivedGeometry/ | 未実装 |
| D_qc と降下模型の同値 | DerivedGeometry/ | 未実装 |
| T1・T1′ | DerivedGeometry/ | 未実装 |
| T2 | DerivedGeometry/ | 未実装 |
| T3 | DerivedGeometry/ | 未実装 |
| 平坦係数の RHom 比較 | DerivedGeometry/ | 未実装 |
| moduleCompact_iff_perfect | 既存 DifferentialGraded/Perfect/CompactConverse | 読み取り専用の接続点 |
| localPerfectQuotientEquivalence | 既存 DifferentialGraded/Quotient/DerivedComparisonPerfect | 読み取り専用の接続点 |
| tildeEquiv | Mathlib AlgebraicGeometry/Modules/Tilde | 読み取り専用の接続点 |
