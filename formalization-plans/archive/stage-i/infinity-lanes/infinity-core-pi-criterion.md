# Ind-π: coherent filtered 空間余錐の π 判定

開始: 2026-10-26 JST。D の最終指定型への定理の実装・最終監査が完了。
停止条件: 二段目完了・設計変更提案・閉包破損・24時間。

## 所有と規約

- 新規葉 `SerrePositivity/InfinityCategories/F2/FilteredExchange/PiCriterion/`（32葉）。
- 独自集約 `PiCriterion/All.lean`、`scripts/audit_f2_pi_criterion.lean`、本計画（≤300行）。
- 他レーンの葉・集約は編集しない。import は既コミット公開モジュールのみ。
- 新 sorry/axiom/citation なし。`ModelCategory SSet` 不使用。
- D の公開入力 `854212ffc`（10:25）と12:02の主判定確認・特殊化指示を直接消費。

## 供給する公開定理

公開名:
`SerrePositivity.InfinityCategories.F2.PiCriterion.dgBarCompactFilteredSpacePiBridge`

所在:
`SerrePositivity/InfinityCategories/F2/FilteredExchange/PiCriterion/FilteredSpaceBridge.lean`

型:

```lean
theorem dgBarCompactFilteredSpacePiBridge
    (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    DGBarCompactFilteredSpacePiBridge.{u, v} κ
```

これは追加の供給仮定なしに、D の元の型
`DGBarCompactFilteredSpacePiData F c → IsColimitCone c` を結論する。
I : Type u は κ-filtered poset、w = max (u+1) v。
F : uliftFunctor.{w+1,u}.obj (nerve I) ⟶ SpaceInfinity.{w}、c : JoinCocone F。
D の構造を複製しない。n は実際の正次数 n+1、π₀ も保持する。
最終葉の保存: `0ae97a051`。独自集約の保存: `ae054fc1f`。

## 証明の接続

1. `TotalComparison` と `TotalPiCriterion`:
   全空間余錐の native 普遍性から、元の c の余極限性と比較の可逆性を同値にする。
   Kan 射の π₀・全基点正次数の Whitehead 判定を適用する。空の空間も含む。
2. `NativeTotalComparison` と `CoconeLegNaturality`:
   元の coslice 比較辺と底の指定辺の実二単体から、脚・transition の Homotopy を得る。
3. `TotalLegFiberComparison`:
   小さい fiber 比較の順方向を持ち上げて厳密に回収し、元の単位の全同型と合成する。
   `totalLegToKan_homotopy_valueToTotal` が有限検出の値射と実際の脚を比較する。
   `finite_nativeTotalLeg_detection` は元の native 頂点値への任意の有限射を一つの実脚で検出。
4. `PairValueRepresentatives` と `BridgePositiveInjectivity`:
   二球面を基点で貼った有限 pushout を一度だけ検出し、同じ stage・基点・path を取る。
   q の像の等式を同じ経路で段階へ戻し、D.positive_equal_at_stage で単射性を得る。
5. `BridgePathTranspose`、`BridgePathRealization`、`PathVertexEdge`:
   D の指定辺の球面円柱と、その同じ辺の path 頂点の群の類を双方向に比較する。
   任意の path 頂点も元の両端を保つ実辺に戻せる。
6. `PiPathSphereComparison` と `PathMapSurjectivity`:
   path による類の比較を自由な球面ホモトピーと同値にし、対称性・推移性を証明する。
   比較射の正次数全射性は、始域の実際の path の両端で不変。
7. `BridgePositiveSurjectivity`:
   脚と段階の移送を合成して実辺 e を取り、D.positive_surjective の全称量化を
   その同じ e に適用する。固定辺の移送の一意性により像が一致し、全基点全射性を得る。
   D の条件を自由 path の存在だけへ弱めない。
8. `BridgeFiniteCriterion` と `CoherentNativeCriterion`:
   D の π₀ 条件と正次数の両方向を `KanMapPiCriterion` にまとめる。
   `isColimitCone_of_coherent_spacePiData` が元の実脚と底の辺へ代入して native 余極限性を結論。
9. `UniverseShape`、`RestrictionLeg`、`FilteredSpaceBridge`:
   B := uliftFunctor.{w,u}.obj (nerve I)、r := ULift.up ∘ nerveEquiv.symm。
   r の全射性、κ-filtered nerve の filtered 性、ULift の保存を使う。
   二段 ULift と一段 ULift の同型に沿って F,c を移す。
   制限余錐の頂点は定義上同じで、脚の全辺は `coconeTransportLeg_restrict` で厳密に一致。
   段・transition は読み戻し後に定義上同じとなり、D の五条件を持つ同じデータを渡せる。
   同型による制限から元の c の余極限性へ戻す。

## 検証

- 全32葉と独自集約の `lake build` に成功。
- 最終定理を `DGBarCompactFilteredSpacePiBridge.{u,v} κ` として直接使う example を監査に追加。
- `scripts/audit_f2_pi_criterion.lean` は最終定理の型・公理と担当全宣言の推移的公理を監査する。
- 最終集約ビルド: `/tmp/pi-final-all-build.log`。
- 最終公理監査: `/tmp/pi-final-audit.log`。
  `PiCriterion audit passed: 219 declarations, standard three axioms only.`
  最終定理も `propext, Classical.choice, Quot.sound` のみ。
- 外部 repo import 閉包2952本に未コミット・編集中の入力なし。
- Derived の入力は許可された `FilteredSpaceBridgeInput.lean` の1葉のみ。
- 担当ソースの sorry/axiom/citation・ModelCategory SSet の使用検査と `git diff --check` に成功。

## 引き継ぎ（分担完了・停止）

- ユーザーが最終定理を確認し、D へ中継済み。本レーンの分担は完了し、ここで停止する。
- R 候補: 抽象構造 `DGBarCompactSpacePiData` を Derived から F2 へ降ろす。
  現在は許可された公開入力 `Derived/CoherentBar/Compact/FilteredSpaceBridgeInput` を直接 import。
  将来の整理で構造を F2 に置き、D 側がそれを import する形へ変更する。今回の分担では実施しない。
- 既存 coherent total API の宇宙分離の複製は不要だった。
  底の ULift と二重持ち上げの同型だけで指定宇宙へ到達する。
- 元の c についての全空間 π 判定の iff と、D が指定した元ごとの十分条件の供給を区別する。
- 本レーンは D の最終指定型への供給まで。他レーンの消費箇所や既存集約は編集しない。
