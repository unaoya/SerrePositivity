# D-bar：D-8 c・工程B（native 余錐と全 Hom）

## 引き継ぎ（2026-10-26）
### 現在地
- 指定の foundations §6・§8、progress の D、D 計画の D-8 c を確認。
- MC は D の公開型そのものの仮定。実 bar 加群、全次数 Hom 同値、twisted 微分、閉列方程式を実装。
- 所有 All のビルド成功（4680 jobs、169葉）。専用公理監査成功（1513宣言、標準三公理のみ）。
- 非退化・退化 graded 因子の分裂と恒等射の二射影分解、退化次数 −1 作用素を構成。
- 実 bar 自己 Hom の MC 微分公式、実微分の境界による段階的射と恒等への全 dg 自然な鎖ホモトピーを供給。
- ラベル自由加群へ Mathlib の PInfty・homotopyPInftyToId・正規化 Moore 同値を直接適用。
- 元の theta の全退化列の非退化射影像が零であることを証明。
- 同じ MC 仮定のみで実正規化 dg 加群と、元の実 bar からの閉零射影を構成。
- 単体次数の標的支持により有限段階と累積ホモトピーが各単体上で安定することを証明。
- 安定値の実 bar 鎖自己写像と恒等への全 dg 自然な鎖ホモトピーを構成。
- D の公開 MC 定理（1017d8a9c）を代入した無条件版を所有葉 Unconditional に追加。
- 19:40 採用の正規化中間模型を保持。同じ theta の変形 retract は D の担当。
- 工程B：正規化実 bar の全次数 Hom・非退化列の微分同値、実 native 列と退化消滅を構成。
- D の Bianchi データを再利用し、全 HA 単体 NativeSimplex と全末端成分のラベル比較を構成。
- 全単調写像に対する自然性と正規化 native JoinCocone を構成（無条件版も公開）。
- 全次数の native 成分写像の線形同値と閉列微分の対応を証明。
- 任意の native 余錐の全成分を復元する閉加群射 UniversalMap と成分による一意性を構成。
- 高次余錐族の混合 HA 単体、二変数自然性、次数 −m の Hom 回収と成分一意性を構成。
- 元の単体・パラメーターの両方の退化消滅と、全混合部分集合の係数比較を証明。
- 回収した Hom の Leibniz 則と、HA 全体右辺の二区間の有限和表示を供給。
- 全混合成分を高次 Hom と native 成分の合成へ同定。元の単体側の削除・左右切断・各項の比較を証明。
- 元の単体側の有限和を、高次 Hom と native 列の微分の合成へ同定（CoconeFamily_source_sum）。
- パラメーター側の削除・切断・各項・有限和を標準面の符号付き和へ同定。
- 全 HA と Leibniz 項を相殺し、回収した Hom の正次数の境界式と零次の閉性を証明。
- 全面・退化と可換な実 pinched Hom 比較射と、全次数の単射性を構成（無条件版を併設）。
- 線形成分から全混合 HA 単体・余錐族そのものを復元する外延性を証明。
- 任意の pinched 線形単体から逆構成の全 join 単体データと左右の制限を構成。
- 比較射の像で全 HA 単体の回収を証明。任意入力の両区間の HA 和を因数分解。
- 任意の pinched 線形単体から作った逆データの、全頂点集合での HA 方程式を証明。
- 全部分集合の HA 方程式と全面・退化の二変数自然性を証明し、実逆 HA 単体を構成。
- 実逆余錐族を束ね、全単体での両逆則と coconeMappingSpace ≅ 実 pinched Hom を構成。
- 公開 MC を代入した同型も供給。指定 native 余錐の IsColimitCone への接続は未完。
- c2・c6・c7 は D の担当。自レーンの完了判定対象外。
### 残り（依存順）
- 1. 工程A：変形 retract は D に移管。CoherentBar/Retract/ の新規葉は読み取り専用。
  正規化加群の公開型は維持。変更が必要なら実施前にユーザーへ報告。
- 2. 工程B：D-bar は正規化側の native 余錐と全 Hom の普遍性に専念（8–24時間）。
- 3. 工程C1/C2：strict 擬同型と比較の組み立ては D-e に移管。StrictComparison/ は読み取り専用。
  読み取り専用 KappaCovers.StrictComparison の DGKappaStrictFilteredColimitComparison R D κ の値として公開する。
  添字は Type u の κ-filtered poset。c2 もこの比較から導く。
  ∞ 圏から poset への共終性は後段の Ind.exists_cofinal_kappaFiltered_poset が担当。
- 4. c2 は D に移管。D が比較を仮定引数として前倒しで構成する。
- 5. c6・c7 も D に移管。D-bar は工程Bの全写像空間の普遍性の完了で公開名を報告し停止する。
- 6. 自分の集約・監査・限定コミット（1時間）。
### 主要宣言
- dgCoherentBarMaurerCartan、dgCoherentBarModule、dgCoherentBarModule_d。
- dgCoherentBarHomDegreeEquiv、dgCoherentBarHomDegreeEquiv_d、dgCoherentBarHomColumnsEquiv。
- dgCoherentBarClosedColumnsEquiv、dgCoherentBar_native_degenerateTriangle。
- dgCoherentBar_raw_inclusion_ne_zero。
- dgCoherentBarNormalizedGraded、dgCoherentBarGraded_identity_decomposition。
- dgCoherentBarNormalizationStageHomotopy、dgCoherentBarEndRebase_d。
- dgCoherentBarLabelNormalizedEquiv、dgCoherentBarLabelProjection_eq_zero_of_degenerate。
- dgCoherentBarColumn_degenerate_normalizedProjection、dgCoherentBarNormalizedTheta_projection。
- dgCoherentBarNormalizedTheta_maurerCartan、dgCoherentBarNormalizedModule。
- dgCoherentBarNormalizedModuleProjection、dgCoherentBarNormalizationBoundary_cycle。
- dgCoherentBarNormalizedHomDegreeEquiv／NormalizedHomColumnsEquiv／NormalizedClosedColumnsEquiv。
- dgCoherentBarNativeColumn、dgCoherentBarNativeColumn_degenerate／vertex_closed／d_positive。
- dgCoherentBarNativeSimplex、dgCoherentBarNativeSimplex_front／last。
- dgCoherentBarNativeSimplexData_last_hom_heq。
- dgCoherentBarNormalizedNativeCocone／NormalizedNativeCoconeUnconditional。
- dgCoherentBarNativeHomUniversalColumns／NativeClosedHomEquiv。
- dgCoherentBarCoconeUniversalMap／UniversalMap_unique／UniversalMapUnconditional。
- dgCoherentBarCoconeFamilyHom／FamilyHom_unique／FamilyHom_columns。
- dgCoherentBarCoconeFamilySimplex_mixed_hom_heq／FamilyHom_parameter_degeneracy。
- dgCoherentBarCoconeFamily_parameter_sum／FamilyHom_differential／FamilyHom_closed_zero。
- dgCoherentBarCoconeHomSpaceComparison／CoconeHomSpaceComparisonUnconditional。
- dgCoherentBarCoconeFamily_ext／CoconeHomSpaceComparison_injective。
- dgCoherentBarInverseRawData／InverseRawData_recovery／Inverse_source_sum。
- dgCoherentBarInverse_parameter_sum／InverseFullHom_differential／InverseRawData_full_equation。
- dgCoherentBarInverseSimplex／InverseSimplex_map／CoconeHomSpaceInverse。
- dgCoherentBarCoconeHomSpaceIso／CoconeHomSpaceIsoUnconditional。
- dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence。
- dgCoherentBarNormalizedNativeCocone_isColimit_of_cosliceComparison（C は明示入力）。
### 依存と提供
- D の既存 Derived・DGNerve・DifferentialGraded と KST/NonConnective は読み取り専用。
- dgCoherentBarTheta と moduleMaurerCartan を使用する。
- c2・c6・c7 の実施と完了判定は D に委ねる。
- 公開 MC 定理を代入した比較・同型の無条件 API を併設。
- 編集所有は Derived/CoherentBar/（Retract/・StrictComparison/ を除く）、その All、専用監査、本計画のみ。
### 未コミット
- 固定終点判定・native 恒等成分・持ち上げ余錐の座標／源側 HA 残差を検証して限定保存する。
### 既知の問題
- 固定終点ごとの全写像空間同型と native 余錐の恒等成分は構成済み。native IsColimitCone は未完。
  指定 native 余錐からの標準 Hom の族との接続を省略しない。
- 変形 retract と strict 比較の実施・完了判定は、それぞれ D と D-e に委ねる。
- MC 仮定付き API を保持し、公開 MC 定理を代入する無条件 API を併設。
### 次の一手
- 05:54 の回答に従い、固定終点で標準 Hom の族と既存の右 Hom 比較を照合する。
- 試行開始 2026-10-26 05:55:47 JST、期限 08:55:47 JST。期限で未完なら承認済み C へ移る。
- 標準 Hom の持ち上げで動く右面を保持した HA 座標を読み、源側の全項を相殺するところまで検証。
  CoconeLiftResidual は回収 Hom の微分とパラメーター側の残差を同定する。

## 採用された設計追加（19:40）
- 根拠：dgCoherentBarIndex は退化を含む全単体を独立因子にする。
  dgCoherentBar_raw_inclusion_ne_zero は非零因子の包含が零にならないことを示す。
  一方 dgCoherentBar_native_degenerateTriangle は任意の native 図式の退化三角形の
  最上 cochain が零であることを示す。生の因子包含を余錐の全高次成分にする直接案は退化を保存しない。
- 提案：既存 theta と実 bar 加群を保持し、所有葉内に正規化した中間模型と
  退化部分の縮約（変形 retract）を構成する。正規化側で native 余錐を作り、
  比較により元の bar へ戻す。Hom 普遍性はまず正規化側とのホモトピー同値で比較する。
- 既存 D の MC 検証に変更は依頼しない。深層編集・模型の置換・追加公理も提案しない。
- Mathlib の AlgebraicTopology/DoldKan を直接参照し、適用可能な API は import して使う。コピーしない。
- 二つの検査補題だけで正規化 retract の存在まで証明したとは扱わない。
- 三段目は報告の六項目で固定。c2/c6/c7 完了とはしない。

## 設計追加と固定終点での先行試行（2026-10-26 05:54 採用）
- 現在の厳密同型は各終点 y の coconeMappingSpace F y と右 pinched Hom を比較する。
  指定した native 余錐からの標準左 Hom の族との同定は未証明。
  この接続を省略して IsColimitCone を結論しない。
- 提案：既存の逆構成を、可変終点の右 HA 単体に対する混合成分へ拡張し、
  `C : sliceUnder (yonedaEquiv.symm nativeApex) ⟶ sliceUnder F` を同じ dg nerve 上で構成する。
  C が恒等余錐を指定 native 余錐へ送ることと、全 fiber の同値性を証明する。
- 接続の正本は所有葉 NativeColimitCosliceCriterion の
  dgCoherentBarNormalizedNativeCocone_isColimit_of_cosliceComparison。
  入力は実 C・射影との可換性・全 fiber の IsQCatEquivalence・恒等余錐の像の等号。
  既存の left fibration の fiber 判定と恒等余錐の始対象性で native 余極限性まで戻す。
  この条件付き判定は証明済みでも、C の存在を供給済みとは扱わない。
- 所有新規葉だけで実施。正規化加群の公開型・元の theta・MC 定理は変更しない。
  D の retract と D-e の strict 比較に変更を依頼しない。模型圏 instance・新規公理も加えない。
- 概算：可変終点の削除／切断・全部分集合 HA・C の組み立て・fiber 同値に追加8–16時間。
  元の単体側の混合因数分解と全部分集合移送は既存の所有補題を再利用する。
- まず固定終点 H y := 右 pinched Hom と q := CoconeHomSpaceIso.hom を使い、
  CoconePointHomInitiality の標準 Hom の族の合成が同値であることを試す（上限3時間）。
  単体ごとの既知の同値との一致、または π₀ と各基点の全 π_n の同型でよい。
- 期限内に通らなければ上記 C の構成を採用して続行する。追加承認は不要。

## 運用
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 等の instance を置かない。
- F2.Compact.IsKappaCompact.{u, max (u+1) v} を使う。
- 深層・既存 D 集約・両監査・他レーンを編集しない。
- 自分の集約と監査のみ検証。根のビルド・.lake 削除はしない。
- set -o pipefail と git commit --only によって所有ファイルだけ保存する。
- 停止は工程B完了（最新分担）・設計変更提案・所有 import 閉包破損・稼働24時間。
- 提案・依頼はユーザーへ中継する。実施記録はコミット本文。
