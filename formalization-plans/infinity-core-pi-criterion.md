# Ind-π: coherent filtered 余錐の π 判定

開始: 2026-10-26 JST。停止条件: 二段目完了・設計変更提案・閉包破損・24時間。

## 所有と規約

- 新規葉 `SerrePositivity/InfinityCategories/F2/FilteredExchange/PiCriterion/`。
- 独自集約 `PiCriterion/All.lean`、`scripts/audit_f2_pi_criterion.lean`、本計画（≤300行）。
- 他レーンの葉・集約は編集しない。import は既コミット公開モジュールのみ。
- 新 sorry/axiom/citation なし。`ModelCategory SSet` 不使用。
- D の確定型を受領。公開入力 commit `854212ffc`（10:25）。後述の型を直接消費する。

## 目標

κ : Cardinal.{u}、κ-filtered poset I : Type u、w = max (u+1) v。
F : uliftFunctor.{w+1,u}.obj (nerve I) ⟶ SpaceInfinity.{w} と
c : JoinCocone F の native 余極限性を、全基点の KanHomotopyGroup の
filtered 余極限条件で判定する。正次数の添字 n は実際の次数 n+1。
空の空間を含めるため、π₀ の条件を省略しない。

## 実装順

1. 全空間の普遍余錐から c への指定比較と、その頂点での可逆性判定。
2. Kan 射の π₀・全基点正次数の Whitehead 判定。
3. 全空間への有限射の fiber 検出を、代表元と等式の有限段階検出へ接続。
4. 基点輸送と共通上界を保持し、D の指定する元ごとの条件を証明。
5. 宇宙分離、元の c への iff、集約と推移的公理監査。

## 確認した公開 API

- `coherentDiagramTotalCocone_isColimit`: 任意の小さい底に native 余極限。
- `nativeCoconeHomApex_isIso` と
  `isColimitCone_of_nativeCoconeHomApex_isIso`: 同じ余錐比較の頂点で判定。
- `coherentFilteredTotalKan_finite_value_detection`: 任意の有限 K の射は、
  ある値からの射とホモトピック。基点固定・段階間の等式は別途必要。
- `continuousKanReplacement_anchored_finite_factorization`: 元の境界を厳密に保持。
- `homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective`: 空の場合も扱う。
- 上記の主要4定理の公理閉包は `propext, Classical.choice, Quot.sound` のみ。

## 宇宙と残課題

既存 coherent total API は底 SSet.{u} と SpaceInfinity.{u} が同じ宇宙。
最終型は底 u・値 w。ULift による底の移送と二重持ち上げ同型を先に検討する。
既存 API の複製が必要となれば R 候補としてここに記録する。
有限射の非相対検出だけから、指定基点での群の全射性・単射性はまだ結論しない。

## 実装済み

- `TotalComparison`: 全余錐から指定比較を取り、頂点の IsIso と元の余極限性の iff。
  普遍余錐同士の場合は `colimitVertexIso.hom` と同じ射であることも証明。
- `KanMapCriterion`: π₀ の全単射と全基点 KanHomotopyGroup.map の全単射を明示。
  空の始域を含む実際の Kan ホモトピー同値との iff。
- `TotalPiCriterion`: 同じ頂点比較の実辺を読み戻した Kan 射による
  `isColimitCone_iff_totalPiCriterion`。filtered 性はまだ不要な段階。
- `UniverseShape`: 底の ULift の後の二重持ち上げと一重持ち上げの厳密同型。
  元の余錐を同型で制限すると native 余極限性が保存・反映される。
- `FiniteDetection`: 任意の有限 K の内部 Hom の π₀ の元は、一つの元の値から来る。
- `PathTransport`: 指定された path 対象の頂点に沿う正次数の群の同値と両端計算。
- `ConstantBoundaryDetection`: 指定点を持つ有限境界が点に因子化することを保って
  一つの実際の fiber へ移す。強変形 retract で fiber の Kan 置換を除去する。
  最終比較は非相対 Homotopy であり、これだけで正次数の群の等式とは主張しない。
- `SphereClassPath`: 非基点固定の球面ホモトピーの指数転置から、両端の群の類が
  同じ path 対象の一つの群の類で得られることを証明。単体上の非相対ホモトピーと区別。

## D の確定条件（ユーザー経由）

`Derived/CoherentBar/Compact/FilteredSpaceBridgeInput` を直接 import してよいとの指示。
供給すべき結論は `DGBarCompactFilteredSpacePiBridge.{u, v} κ`：
元の F,c に対する `DGBarCompactFilteredSpacePiData F c → IsColimitCone c`。
`[Fact κ.IsRegular]`、`[IsCardinalFiltered I κ]` を保持する。
`DGBarCompactSpacePiData` を複製しない。抽象構造を F2 へ降ろすことは R 候補。

- π₀: 候補頂点の各頂点はある段階の頂点から道で来る。
  段階の二頂点の候補頂点内での同一視は、共通の後続段階で起こる。
- 正次数: i の基点 y ごと、候補頂点への群写像が j≥i への押し出しと
  基点移送を含めた元ごとの全射・単射を満たす。
- 群の圏の余極限は使わない。
- 指定辺に沿う移送は `dgBarCompactPiTransport`：境界がその辺をたどる球面円柱。
  自由な path の存在だけへ弱めない。`positive_surjective` は返す代表に対して全ての辺を量化。
- strict 版の参考 `KST/Spectra/FilteredHomotopyGroups.pointedHomotopyGroupColimitIso`。

## 次の作業

1. `SphereSimplex.equiv` で任意の正次数の類を有限球面射にし、
   `coherentFilteredTotalKan_finite_value_detection` と `sphereClass_path_witness` を合成。
   これにより、元の指定基点から段階の像への実際の path と群の代表を同時に得る。
   球面の有限性は既公開 `KST/Spectra/FilteredLoopColimit.pointedSphere_finite`。
2. 群の等式を相対球面ホモトピーとして有限検出し、poset の共通上界へ押す。
   既公開の有限 Homotopy 検出だけでは、指定基点・元の transition との整合性は未完。
3. 元の余錐の脚と全空間比較の可換性を、同じ余錐比較の coherent 辺から回収。
4. 確定した D 型の消費定理、宇宙 w の最終型、κ-filtered poset の特殊化を接続。

## 継続作業（進行中）

- `SphereClassPath` に任意の類の球面代表と元の射を保持する pointed image を追加。
  commit `2e75cd20c`。
- `PositiveValueRepresentatives`: 正次数の全空間の類を元の値と実際の path の群の類で表す。
- `PiZeroRepresentatives`: π₀ の全空間の各成分に元の値の代表を取る。
- `LiftedTotalPiCriterion`: 宇宙を分離した元の余錐の余極限性と全空間 π 判定の iff。
- `PiPathRelation`: 自由な path による類の比較と基点表示の変更、後合成の自然性。
  D の指定辺の条件そのものではなく、構成の中間補題。
- `BridgeComponents`: D の構造を直接消費し、代表・脚の可換性・transition の自然性から
  比較射の π₀ の全単射性を導く。元の coherent 図式での可換性の入力は未接続。
- 以上5葉のビルド成功。全62宣言の標準3公理監査に成功。
- `BridgePathTranspose` の球面円柱の転置と、同じ指定辺の移送の左右の一意性がビルド成功。
- `PositiveVertexRepresentatives` は元の指定頂点 x を基点とする任意の類に、
  元の値の類と実際の path を返す。構成上の ofVertex の基点表示を除去済み。
- `PathFamilyHomotopy` は指定 path の族をそのまま円柱へ戻し、源への制限と厳密に可換。
- 上記3葉を含む全86宣言の標準3公理監査成功。commit `7586484ac`。
- `BridgePathRealization` がビルド成功。指定辺の path 頂点の群の類から D の球面円柱へ
  戻す逆向きと、`dgBarCompactPiTransport n e a b ↔ bridgePiTransportEquiv n e a = b` を証明。
- 外部の repo import 閉包2811本に未コミット・編集中の入力なし。
- `BridgePathRealization` を含む全98宣言の標準3公理監査成功。
- `PairValueRepresentatives`: 共通基点で貼った二球面を一度だけ有限検出し、二つの類を
  同じ stage・同じ基点・同じ path 頂点の二つの類で表す。commit `d71cbe468`。
- `PairPathEquality`: 共有 path の両端の等式は後合成後も同値。
  基点を固定しない Homotopy でも、二つの類を同一視する条件は不変。commit `3d87459e0`。
- `NativeTotalComparison`: coslice の実際の比較辺から頂点射を取り、元の各脚との
  合成 Homotopy・π₀ の可換式・正次数の等式条件の同値を供給。commit `4b8fae870`。
  この実際の比較についても余極限性と全基点 π 判定の iff を証明。
- `CoconeLegNaturality`: 底の元の指定辺と余錐頂点の join 二単体を構成し、
  同じ脚と元の transition の合成 Homotopy・π₀ の可換式を供給。
  成分の系では投影 Kan 型の展開により標準 heartbeat を超えたため、局所的に上限を増加。
- `BridgeStageKernel`: D.positive_equal_at_stage を直接消費し、段階に Homotopy まで自然な
  任意の Kan 標的で元の二つの類の像が等しいことを証明。上の自然性と合わせて使用。
  この葉と `CoconeLegNaturality` の保存: `e878fa9e0`。

## 確定型への残る接続

1. `NativeTotalComparison` と `CoconeLegNaturality` により、元の余錐の実際の脚を使う
   hcomm・hstage の Homotopy は構成済み。有限検出の valueToTotalKan と標準余錐の脚を結ぶ。
2. 正次数の単射性は、二つの球面の基点を貼った有限 wedge の同時検出を使う。
   その有限 wedge の同時検出は `total_positive_pair_representative` として証明済み。
   一つの H の指数転置は二代表に同じ path 頂点を与えるので、q の像での等式から
   stage の脚の群の等式を得る。D.positive_equal_at_stage で後続段へ移して T で等式を反映。
3. 正次数の全射性は D.positive_surjective（全ての指定辺）と全空間側の実際の path を組み合わせる。
   指定辺を保つ必要がある箇所は BridgePathRealization の iff を使い、自由 path の存在へ弱めない。
4. 小さい底の持ち上げ、I の CardinalFiltered から filtered 性、元の脚・transition の
   持ち上げとの一致を接続し、追加の供給仮定のない DGBarCompactFilteredSpacePiBridge を結論にする。
   この最終結論はまだ未証明。現在の補題をその代替として完成扱いにしない。

## 検証と保存

- 初期入力監査: `/tmp/audit-pi-inputs.lean`、主要4定理とも標準3公理のみ。
- 22葉は個別の `lake build` に成功。独自集約も全葉の公開に更新済み。
- 初期38宣言から全138宣言へ監査範囲を拡大し、いずれも標準3公理のみ。
- `lake build SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.All` 成功。
- `lake env lean scripts/audit_f2_pi_criterion.lean` 成功:
  `PiCriterion audit passed: 138 declarations, standard three axioms only.`
- 外部の repo import 閉包2821本に未コミット・編集中の入力なし。
- 基礎5葉と初期計画: `591c62fdb`。π接続・定数境界・球面path: `7cbc996e4`。
- 独自集約: `4b511d49e`。監査と本チェックポイントを追加保存。
- 代表元・D零次数: `eb3233ea3`。指定辺の転置と元の基点: `7586484ac`。
- D移送の群同型による双方向表示: `6492709fb`。その時点の独自集約: `024dd5e84`。
- 共通基点二球面から元の余錐脚の自然性まで5葉を追加。現行独自集約: `3584886ff`。
- 既存 API の宇宙分離の複製は現在なし。D 入力の抽象構造を F2 に降ろすことは R 候補。
- 最終目標の達成は未宣言。正次数の代表と同一視の filtered 段階整合性が残る。
