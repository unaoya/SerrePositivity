# K-L4：導来圏と幾何の基盤

> **休止（2026-10-19）**：基盤に集中する決定により第 II 段で再開。引き継ぎ節を正本として保持。dg 圏の一般論（§26）は D レーンが読み取り専用で使う。

## 引き継ぎ（2026-10-19）

### 現在地

- K-L4（導来圏と幾何の基盤）。§26 採用の一般 dg 半自由分解・Hom の K-flat 性・準同値の移送・商の H⁰ 比較は実装済み。
- 実際の全係数加群層の導来圏を用いた bounded below アフィン Dqc 同値まで完了。
- 任意の Grothendieck アーベル圏の非有界 K-injective 分解の存在を証明済み。
- 非有界 RΓ と tilde の導来随伴、RΓ のシフト両立・三角性・積保存を構成済み。
- 現工程の区切り：複体・ホモトピー圏・導来圏の積、K-injective な積による導来積の計算。
- 完全な積の下のコホモロジー比較と射影の両立、差分のファイバー三角、全射加群逆系の差分の全射性、前次数の全射性からのファイバーの核の計算まで検証済み。
- 非有界の単位・余単位の同型性とアフィン Dqc 同値は未完。T1 以降も未完。
- 最終検証：対象ビルド 4126 jobs 成功。公理監査 2636 宣言、propext・Classical.choice・Quot.sound のみ、KTheory import なし。
- 実装保存：27fd68df、0aeecdfc、d7fe08b4。最後の区切りは d7fe08b4。

### 残り（依存順、原典番号と時間見積もり）

- 非有界アフィン比較：導来積のコホモロジーの射影との両立と Milnor 型核計算を接続し、基本開上の消滅から E → Rlim τ≥−n E を証明。有界下方比較との両立、単位・余単位の同型性。Stacks 20.37.5–20.37.9・36.3.3–36.3.5、TT §3。目安 16–40 時間。
- T1・T1′：係数付きコンパクト生成、局所有限射影有限複体と perfect 性の一致。Bondal–van den Bergh Thm 3.1.1、TT §3、Toën §3.2。目安 16–40 時間。
- T2：台つき部分圏の生成と局所化、D(X;H)/D_Z ≃ D(U;H) の完全忠実性・本質的全射性。Neeman 1992 Thm 2.1・Cor 3.2.3、TT §3。目安 24–60 時間。
- T3：係数付き切除・Zariski MV、有限アフィン被覆の Čech 降下。TT 3.19・8.1、正本 §10-7。目安 24–60 時間。
- Perf：層の有限アフィン降下模型と Dqc の compact／局所 perfect の同一視・増強。TT §3・§8、Toën §3.2、正本 D4。目安 16–40 時間。
- RHom 比較：平坦 H に対し Čech 複体のテンソルと RHom を比較。TT §3・§8、Toën §3.2。目安 12–32 時間。
- 見積もりは Lean 実装の作業時間の幅であり、未実装の収束基盤の規模次第で増える。

### 主要宣言（名前のみ）

- `DGResolution.quotientTriaEquivalence`
- `DGResolution.perfectQuotientEquivalence`
- `dqcDGHomotopyEquivalence`
- `affineDqcPlusEquivalence`
- `exists_unbounded_kInjective_resolution`
- `kInjectiveDerivedFunctor_isEquivalence`
- `kInjectiveLocalizationAdjunction`
- `unboundedDerivedAdjunction`
- `affineDerivedΓ`
- `affineDerivedAdjunction`
- `affineDerivedΓ_isTriangulated`
- `affineDerivedΓ_preservesLimits`
- `derivedKInjectiveProductIsLimit`
- `complexProductHomologyIso_hom_π`
- `complexProductHomologyIsLimit`
- `sequentialLimitTriangle_distinguished`
- `exists_lift_sequentialLimitTriangle`
- `sequentialDifference_epi_of_surjective`
- `derivedTriangleHomologyKernel`

### 依存と提供

- 読み取り専用：Mathlib AlgebraicGeometry／SheafOfModules／DerivedCategory、既存 DifferentialGraded の dg 商・perfect・Yoneda、CategoryTheory.VerdierLift。
- K-L1b・L3 へ：DGResolution 内の任意の DGCategory に対する半自由分解、フィルトレーションによる K-flat 性、準同値と商の移送。
- K-L5・後継 K-導来幾何へ：実際の係数 Dqc と dg 増強、bounded below アフィン同値、非有界分解・導来随伴・積計算の基盤。
- Dqc／Perf の局所化・降下は本レーンの提供予定。非有界アフィン同値と T1–T3 を既提供として使わない。

### 未コミット

- 実装の未コミットはなし。この引き継ぎ節も計画ファイルだけを別コミットで保存する。
- 他レーンの変更・ルート集約の変更は編集もコミットもしていない。

### 既知の問題

- 現在、自分の import 閉包のビルド失敗・名前衝突はない。先の工程区切りの全体ビルドも 13722 jobs 成功。
- 古い root build の relativeFunctorVertex 重複は最終の全体ビルドでは再現しなかった。他レーンの将来の状態は未保証。
- `ModelCategory SSet` の instance 仮定は本レーンにない。一般定理には明示的な `HasDerivedCategory` 等の Mathlib の型・圏の仮定が残る。
- 全層の導来圏一般の左完備性と層の積の完全性は仮定できない。§62 の準連接コホモロジーとアフィン基本開の消滅を使って収束を証明する必要がある。
- D(QCoh) のアフィン同値を、全層の導来圏内の Dqc の非有界同値の代用にしない。
- H は非可換も許し、平坦性は RHom 比較まで追加していない。分解・収束の存在を構造体の未証明フィールドにしない。
- 既存・今回の Lean ファイルに style／unusedSectionVars の警告はある。エラーと追加公理はない。

### 次の一手

- §62 と Stacks 20.37.5–20.37.9・36.3.3–36.3.5 を読み、検証済みの積コホモロジーの射影公式とファイバー核計算から Milnor 型比較を接続する。次にアフィン基本開上の局所判定で切断塔の収束を閉じる。
- 非有界アフィン比較を閉じるまでは T1 を開始しない。所有範囲、対象ビルド、公理監査、git commit --only を維持する。


作成日：2026-10-18。状態：L4a 途中。§26 の設計変更に基づく一般 dg 圏の半自由分解・K-flat 性・準同値の移送・層導来圏との比較は実装済み（§27–33）。

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

- 現在地：L4a の係数環層・準連接性・開埋め込みの比較と、アフィン大域切断の忠実性・同型反映は証明済み。任意 dg 圏の半自由な段階分解、フィルトレーションからの Hom の K-flat 性、増大関手の各次数全射性・準同値性・H⁰ 同値、前三角化の三角同値を証明済み。分解後の層の acyclic dg 商自体の H⁰ と Mathlib の元の層導来圏の同値、対象ごとの導来像の計算、準連接コホモロジーによる Dqc への H⁰ 同値を証明済み。半自由分解から導来比較までの工程は完了。アフィン準連接係数加群層と左 H 加群の通常の圏同値、その準連接複体の導来圏の三角同値、実際の Dqc の開制限、台つき核と Verdier 商への降下も証明済み。Perf、アフィン導来比較、導来降下、T1–T3、平坦係数の RHom 比較は未完了。
- L4b の入力である層の随伴と導来忘却は実装済み。L4b の随伴移送の一般定理は証明済み。実際の導来随伴・生成・T1′、L4c の局所化同値、L4d、L4e は未完了。
- 最新の検証済み保存単位は対象ビルドと所有 namespace の1,668宣言の公理監査に成功。工程区切りの全体ビルドは有限 Čech 完全性までの状態で11,343 jobsに成功。許容公理は標準3公理のみ、KTheory import なし。
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

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L4-derived-geometry-log.md](../../L4-derived-geometry-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
