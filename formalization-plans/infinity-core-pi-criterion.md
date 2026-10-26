# Ind-π: coherent filtered 余錐の π 判定

開始: 2026-10-26 JST。停止条件: 二段目完了・設計変更提案・閉包破損・24時間。

## 所有と規約

- 新規葉 `SerrePositivity/InfinityCategories/F2/FilteredExchange/PiCriterion/`。
- 独自集約 `PiCriterion/All.lean`、`scripts/audit_f2_pi_criterion.lean`、本計画（≤300行）。
- 他レーンの葉・集約は編集しない。import は既コミット公開モジュールのみ。
- 新 sorry/axiom/citation なし。`ModelCategory SSet` 不使用。
- D の正確な型は未到着。ユーザーから暫定条件と所在なしの回答を受領（2026-10-26）。

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

## D の暫定条件（ユーザー経由）

- π₀: 候補頂点の各頂点はある段階の頂点から道で来る。
  段階の二頂点の候補頂点内での同一視は、共通の後続段階で起こる。
- 正次数: i の基点 y ごと、候補頂点への群写像が j≥i への押し出しと
  基点移送を含めた元ごとの全射・単射を満たす。
- 群の圏の余極限は使わない。正確な Lean 型の確定は D の報告待ち。
- strict 版の参考 `KST/Spectra/FilteredHomotopyGroups.pointedHomotopyGroupColimitIso`。

## 次の作業

1. `SphereSimplex.equiv` で任意の正次数の類を有限球面射にし、
   `coherentFilteredTotalKan_finite_value_detection` と `sphereClass_path_witness` を合成。
   これにより、元の指定基点から段階の像への実際の path と群の代表を同時に得る。
   球面の有限性は既公開 `KST/Spectra/FilteredLoopColimit.pointedSphere_finite`。
2. 群の等式を相対球面ホモトピーとして有限検出し、poset の共通上界へ押す。
   既公開の有限 Homotopy 検出だけでは、指定基点・元の transition との整合性は未完。
3. 元の余錐の脚と全空間比較の可換性を、同じ余錐比較の coherent 辺から回収。
4. D 型の確定後に条件の消費定理、宇宙 w の最終型、κ-filtered poset の特殊化を接続。

## 検証と保存

- 初期入力監査: `/tmp/audit-pi-inputs.lean`、主要4定理とも標準3公理のみ。
- 8葉は個別の `lake build` に成功。`TotalPiCriterion` も成功。
- 初期4葉の17宣言は標準3公理のみ。全8葉の監査を追加実行中。
- 外部の repo import 閉包2004本に未コミット・編集中の入力なし。
- 基礎5葉と初期計画: commit `591c62fdb`。続きの葉・集約・監査は保存中。
- R候補の既存 API 複製は現在なし。
- 最終目標の達成は未宣言。正次数の代表と同一視の filtered 段階整合性が残る。
