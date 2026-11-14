# SC-W1 2g-1：非 Noether 基底への接続の境界

2026-11-14、math/scheme。これは停止点 2g-1 の完成報告ではない。

一覧：済み 6／全体 12（うち追加 3）

## 検証済みの区切り

数学の HEAD は `10bb96c88`。A01〜A06 が済み、A07 と B01〜B04 は未完。新たに特定した C01 は追加候補・未実装として台帳に含めた。G0 は別計上。

- G1：本体 737 行、入口の追加込み 761 行。G0 は本体 682 行、入口込み 710 行。G2 は未実装。外枠 25,000 行と途中報告点約 12,000 行には未到達。
- 既存の対象検証：`lake build SerrePositivity.AlgebraicGeometry`、4,808 jobs 成功。
- 同じ数学に対する標準監査：10,700 宣言、`propext`・`Classical.choice`・`Quot.sound` のみ。
- ログは作業木の `scheme-drafts/2g-g1-noetherian-registered-build.log` と `2g-g1-noetherian-registered-audit.log`。この境界調査では Lean を変更せず、ビルド・監査を再実行していない。

## 何が不足しているか

原典照合：Rydh の [Submersions and effective descent of étale morphisms, §3](https://davidrydh.se/papers/submersion20100305.pdf)、Prop. 3.7、Properties 3.9、Thm. 3.10。
非 Noether affine の証明は、TIC からの整全射、一般点集合の準コンパクト性、有限段への降下を使う。Prop. 3.7 の Noether 段の狭義変換は全射とは限らない。全射性は元の基底へ戻して回収する。

したがって、有限表示の f のモデル fᵢ を選んだだけでは、検証済み A06 を適用できない。A06 は fᵢ の v 判定を要求する。その v 判定が有限段に降りるという結論をここで仮定するのは循環になる。

### C01：追加判断が必要な独立した構成の型

完全な TIC の API より弱い、必要な供給の候補は次の型。これは紙の仕様であり、採用済みの Lean 宣言ではない。元の Rydh の TIC 構成をそのまま形式化する代わりに、必要な性質だけを取り出した案である。

```lean
-- 紙の型案。未検証・未実装。
(A : CommRingCat.{u}) [IsReduced A] :
  ∃ (B : CommRingCat.{u}) (i : A →+* B),
    IsReduced B ∧ Function.Injective i ∧ i.IsIntegral ∧
      IsCompact {q : PrimeSpectrum B | q.asIdeal ∈ minimalPrimes B}
```

単射・整性から Spec B → Spec A の全射性を得る。元の環が非被約なら、被約化との合成を使う。この型は f や中心の係数を移す法則ではなく、新しい環 B の存在を供給する。

TIC 全体を作らず、この型だけで必要な入口を満たす案がある。ただし、その実装方法や費用はまだ検証していない。Mathlib の根の存在条件や absolutely integrally closed の語を、TIC の定義や一般点集合の準コンパクト性と同一視しない。

### C01 の後にも残る A07 の接続

1. 準コンパクトな一般点集合を持つ被約 affine 基底で、有限表示射の平坦な準コンパクト稠密開を供給する。
2. 射・その開・平坦性を Noether 段へ降ろす。モデルの v 判定は要求しない。
3. 既存の平坦化中心をその段で作り、引き戻した閉部分スキームが稠密開の逆像の閉包を含むことを示す。特殊化の持ち上げから、引き戻し後の全射性を得る。
4. 整全射を有限・有限表示の段で近似し、細分の有限図式と flat・proper・surjective を共通段にそろえる。

C01 の存在だけでこれらが済んだとはしない。特に Noether な補助射の閉包の像の議論を、非 Noether な基底へ仮定の点検なしに移さない。

## 既存の材料との境界

`rg` による SerrePositivity の代数幾何・可換環論と固定版 Mathlib の該当領域の調査では、TIC や上の C01 に直接一致する API を確認できなかった。文字検索による数学的な不存在の断定ではない。

- Mathlib `AffineTransitionLimit.lean` は既存の有限表示対象への射と等式の有限段表示等を供給するが、C01 の環や一般の有限表示スキームのモデルを作る定理ではない。
- `SpreadingOut.lean` の germ-injective な stalk の射の拡張は、任意の filtered な環の図式への対象の降下の代用にならない。
- このレーンの `exists_surjective_pullback_snd_of_isLimit` は、既に与えられた Noether 段の固有モデルから全射性を降ろす。モデル構成や C01 は供給しない。
- B01〜B04 のモデル構成も未完。有限段の基底への射に忠実平坦性を追加して代用しない。

## 止める理由と代わりの作業

正本 [lane-goals-2026-11-14.md の共通規則](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/formalization-plans/stage-ii/lane-goals-2026-11-14.md) は「止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）、まとまりの外のもの、外枠に届くとき」と定める。C01 は新しい環を供給する独立構成に当たるため、この線の Lean はここで止める。2g-1 を完成扱いにせず、代わりの仕事である [2h の段 0](scheme-w1-2h-route.md) を作成した。

次に判断する対象は C01 を含む束の追加であり、最終主張や Rydh 3.10 の経路の変更ではない。C01 の工数を既存の 761 行から推定することはできない。追加束の実装経路を確定する際、A07 の残りと G2 のモデル構成を合わせて再見積もりする必要がある。
