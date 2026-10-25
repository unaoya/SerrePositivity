# D-bar：D-8 c・工程B（native 余錐と全 Hom）

## 引き継ぎ
### 現在地
- 最新分担の工程Bは完了。正規化 bar の指定 native 余錐の実余極限性を公開した。
- foundations §6・§8、progress の D、D 計画の D-8 c の運用 v3 に従う。
- D の公開 MC 定理を代入した無条件版を併設。
- 公開名をユーザーへ報告し、最新の停止指示どおり停止する。
### 確定三段目（六項目）
1. 工程A：変形 retract は D に移管。CoherentBar/Retract/ は読み取り専用。
2. 工程B：正規化 native 余錐・全写像空間の同型・標準 Hom の族・実余極限性を完成。
3. 工程C1/C2：strict 擬同型と比較の組み立ては D-e に移管。StrictComparison/ は読み取り専用。
   公開述語 DGKappaStrictFilteredColimitComparison R D κ の値として後段で接続する。
4. c2：D が比較を仮定引数として担当。D-bar の完了判定には含めない。
5. c6・c7：D に移管。D-bar は工程Bの完了で公開名を報告して停止する。
6. 所有 All と専用公理監査を検証し、所有ファイルだけを限定コミットする。
### 主要公開API
- native 余錐：dgCoherentBarNormalizedNativeCocone。
- 実余極限：dgCoherentBarNormalizedNativeCocone_isColimit。
- 無条件の実余極限：dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit。
- 全写像空間同型：dgCoherentBarCoconeHomSpaceIso／CoconeHomSpaceIsoUnconditional。
- 標準族の合成の同値：dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence。
- その無条件版：dgCoherentBarNormalizedNativeCoconeUnconditional_pointHomComparison_homotopyEquivalence。
- 固定終点の実回収同型：dgCoherentBarCoconePointFiberIso、同型の hom は CoconePointFiber そのもの。
- 同じ右 Hom 模型への厳密な照合：dgCoherentBarCoconePointFiber_comparison。
### 最終結論の形
- NativeColimit の無条件定理は CommRing R・DGCategory R D・Small D・元の I と coherent F のみを取る。
- 結論は IsColimitCone (dgCoherentBarNormalizedNativeCoconeUnconditional R D F)。
- MC 仮定付き版の仮定は dgCoherentBarMaurerCartan R D F そのもの。
- 無条件版には Derived/DGCoherentBarMaurerCartan.dgCoherentBarTheta_maurerCartan を代入。
- 正規化加群 dgCoherentBarNormalizedModule の公開型を保持。
### 依存と提供
- D の既存 Derived、DGNerve、DifferentialGraded と KST/NonConnective は読み取り専用。
- 元の dgCoherentBarTheta と dgCoherentBarModule を保持。
- D の retract と D-e の strict 比較に変更を依頼しない。
- c2・c6・c7 の実施と完了判定は D に委ねる。
- c2 以降の compact 性は F2.Compact.IsKappaCompact.{u, max (u+1) v} の型を維持する。
- 編集所有は Derived/CoherentBar/ の根の葉、その All、専用監査、本計画のみ。
### 残り
- 工程Bの数学的な未完項目はない。
- 検証と限定保存後、公開名をユーザーへ報告して停止する。

## 証明の接続
- 正規化 native 列は元の単体の退化で零になる。全面・全退化に自然な実 HA 単体から指定 JoinCocone を構成。
- 全次数の Hom は native 列との合成で非退化成分の族と線形同値になる。
- 固定終点の余錐族から高次 Hom を回収し、全 HA 方程式と逆構成により右 pinched Hom との厳密同型を構成。
- 指定 native 余錐から回収する Hom は恒等である。
- 左右 pinched Hom の厳密同型を、dg 反対模型と符号付き線形反転から構成。
- 標準族の持ち上げの実右面を保持し、回収 Hom の非線形微分方程式を証明。
- 全部分集合の HA 方程式と全自然性を使い、余錐族を一点下の実 coslice へ回収する。
- この回収射は同じ dg nerve 上の射影を厳密に保ち、指定 native 余錐を実恒等余錐へ送る。
- 各固定終点で、回収射と左右 Hom 同型の合成は既存の右 Hom 比較に実単体写像として一致する。
- leftFibrationInitialTotalMap の底側の二射影は自明 Kan fibration。
  二射影の同値を消去して中間空間の比較を同値とし、終点評価との厳密可換性で標準族の同値を反映する。
- 各 y で coconePointHomFamily d y ≫ CoconeHomSpaceIso.hom が実ホモトピー同値となる。
- HomotopyLimits.isColimitCone_of_pointHomFamily_comparison に渡して指定 native 余錐の IsColimitCone を得る。
- 最終定理は追加の coslice 比較 C を仮定引数に取らない。

## 採用された設計と分担
- 19:40 採用の正規化中間模型を使用。元の theta と bar 加群を保持する。
- Mathlib の PInfty・homotopyPInftyToId・正規化 Moore 同値は所有葉から直接参照する。
- 元の bar への同じ theta の微分に対する変形 retract は D の工程A。
- strict 余極限への擬同型と比較組み立ては D-e の工程C1/C2。
- DGKappaStrictFilteredColimitComparison は Type u の κ-filtered poset 添字で十分。
  ∞ 圏から poset への共終性は後段の Ind.exists_cofinal_kappaFiltered_poset が担当する。
- 05:54 の指定に従う固定終点の先行経路で結論を得た。
  最終判定には固定終点の標準族と右 pinched Hom の合成の同値性を用いる。
- 条件付き NativeColimitCosliceCriterion は互換用の補助APIとして保持。

## 運用
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 等の instance を置かない。
- docstring は 概要／方針／規約／使われ方。
- 深層・既存 D 集約・両監査・他レーンは編集しない。
- 自分の集約と専用監査だけを検証。根のビルドと .lake の削除はしない。
- set -o pipefail、git commit --only によって所有ファイルだけを保存する。
- 実施記録・検証結果はコミットメッセージ本文に記す。
- 最新停止条件は工程B完了。A・C・c2・c6・c7 へ追加着手しない。
- 提案・依頼が生じた場合は、計画への記載だけでなくユーザーへ中継する。
