# K-L4：導来圏と幾何の基盤

作成日：2026-10-18。状態：L4a 途中。具体的係数環層 H_X とその中心的な構造層作用を構成済み。アフィン模型・降下との比較を整備中。

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

- 現在地：L4a の具体的係数環層 H_X を、構造射 X → Spec A に対するテンソル前層の層化で構成済み。構造層の中心的作用と H の作用の A 上の一致、H = A での構造層の回復も証明済み。tilde の基本開切断のテンソル表示を構成済み。H_X のアフィン切断・dg 模型・降下との比較は未完了。
- L4b の入力である層の随伴と導来忘却は実装済み。L4b の導来随伴・生成・T1′、L4c、L4d、L4e は未実装。
- 最新の検証済み保存単位は対象ビルドと所有 namespace の146宣言の公理監査に成功。許容公理は標準3公理のみ、KTheory import なし。
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

## 設計変更提案：§10-7 の厳密降下と導来降下の区別

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
- 推奨する明確化：降下模型をアフィン導来 dg 加群圏のホモトピー降下とする。
- 対象の遷移は導来同値、射の計算には写像複体とその高次の両立性を保持する。
- 通常の三角圏の同型と cocycle だけを持つ pullback は使わない。
- dg 模型で Čech のホモトピー極限を構成し、実際の D_qc への比較を証明する。
- 局所 perfect な対象をこの比較の両側で対応させ、Perf(X;H) の dg 増強を得る。
- この変更は K 理論への依存・引用・公理・sorry を追加しない。
- この変更は分離性を追加しないので KST の非分離 qcqs の範囲を維持する。
- 代替：任意の係数加群層の複体を厳密に降下し、局所化してコホモロジー条件へ制限する。
- 代替でも、アフィン環の dg 加群との比較を導来化後に証明する必要がある。
- [Toën 原典](https://www.math.univ-toulouse.fr/~btoen/dgazumaya.pdf) §3.2、pp.32–35 に対応を確認した。
- Toën Prop 3.9 は compact local generator の Zariski 貼り合わせを述べる。
- 同 p.34 の局所計算はアフィン開にわたる dg 圏の Holim を明示している。
- 同 p.35 の帰納段階は二開被覆の homotopy cartesian square を用いる。
- 交わり W の被覆枚数に対する帰納はせず、アフィン側から W への compact の持ち上げを使う。
- 持ち上げには Neeman Thm 2.1 と BvdB Cor 3.2.3 の E ⊕ E[1] を使う。
- そのため、有限被覆の枚数が単調に減らないという初期の注意にも整合する。
- 次の降下実装では、この模型の明確化を受けて層の比較と dg の写像複体のどちらから始めるかを固定する。自由忘却随伴・導来忘却のような両模型に共通する基盤は進められる。
- この提案は厳密なアフィン環加群複体の模型に関するもの。任意の加群層の複体に基づく現在の Dqc の定義・係数忘却の実装を止める理由にはしない。
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
- 次は、このテンソル表示の制限射への自然性と H_X への層化比較を接続し、層化後のアフィン切断を同定する。
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
- この線形同型はまだ環層 H_X の切断の同型を述べていない。
- 制限射への自然性、基礎環 A から R への底変換、層化との比較をつなぐ必要がある。
- H = A の係数前層は構造層と自然同型で、すでに層条件を満たす。
- その層化の比較も同型なので、H = A の係数環層は構造層へ標準的に戻る。
- これらを L4a 全体の降下比較や、T1 のコンパクト生成の証明と混同しない。

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
| H_X のアフィン切断とテンソルの比較 | DerivedGeometry/ | 未実装 |
| 層の降下 | DerivedGeometry/ | 未実装・模型の設計変更提案中 |
| D_qc と降下模型の同値 | DerivedGeometry/ | 未実装 |
| T1・T1′ | DerivedGeometry/ | 未実装 |
| T2 | DerivedGeometry/ | 未実装 |
| T3 | DerivedGeometry/ | 未実装 |
| 平坦係数の RHom 比較 | DerivedGeometry/ | 未実装 |
| moduleCompact_iff_perfect | 既存 DifferentialGraded/Perfect/CompactConverse | 読み取り専用の接続点 |
| localPerfectQuotientEquivalence | 既存 DifferentialGraded/Quotient/DerivedComparisonPerfect | 読み取り専用の接続点 |
| tildeEquiv | Mathlib AlgebraicGeometry/Modules/Tilde | 読み取り専用の接続点 |
