# SC-W1 2h：段 0（紙）

2026-11-14、math/scheme。2g-1 の境界で行う代わりの作業。Lean の実装開始や 2g の完成を意味しない。2g の未完の入口を追加仮定として最終出力に残さない。

2g-1 の一覧：済み 6／全体 12（うち追加 3）

2h の一覧：済み 0／全体 4（うち追加 0）。以下の H01〜H04 は段 0 の主項目であり、証明済み宣言ではない。

## 1. 出口と利用側

出口は BS17 Thm. 4.1(i) の、このレーンに指定された affine 構造層・有限族の形。Witt ベクトルの全段や任意の有限射影加群までをこの入口で新しく主張しない。

```lean
-- 最終仕様。ここでは紙の型であり、Lean 本体への宣言追加ではない。
theorem cech_exact_of_vCover_perfect
    (p : ℕ) [Fact p.Prime]
    {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsAffineVCoverFamily B f) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve
```

利用側は `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean` の同名の引用。そちらの `affineFamilyCech` は上の `Arrow.mk ...` と同じ定義で、完全性の述語も増大での単射・第 0 次の完全性・全正次数の完全性である。v 判定は G0 の有限族の定義と同じ試験環・同じ証人を使う。実装時は利用側の型との照合を小さい検査ファイルで行い、drafts を import しない。

[BS17](https://arxiv.org/pdf/1507.06490) の Prop. 4.5 と Thm. 4.1 の証明が通常の F_p スキームと完全スキームを結ぶ箇所に対応する。ただしこのレーンでは、既に承認された Čech 版の中間命題から指定の affine な出力へ直接接続する。導来関手の Hⁱ との比較やサイト全体の同値を追加実装する計画ではない。

## 2. 記法と未完の入口

紙の記法 `P(A)` は、既存の `FrobeniusDirectLimit A p hp hz`。`P(f)` は `frobeniusDirectLimitMap`。`C(f)` は環準同型 f の増大 Čech conerve。`P_* C(f)` は各対象の環に P を適用し、構造写像には同じ P(f) を適用した増大余単体対象である。P は p の像が零の環の圏で扱い、`hz : (p : A) = 0` を保持する。

次の入口は現時点で未完。

- **2g-1**：A07（任意の affine 基底の fppf–proper 細分）、B01〜B04（有限型 F_p の被覆モデル、性質の同時降下、filtered 表示）。追加候補 C01 も未実装。
- **G3**：2d の許容 blowup 細分を帰納と有限ファイバー冪の射影表示へ接続する。
- **G4**：2f の射影 Cartesian 四角形と B1 から、Frobenius 係数での Čech 降下の判定を得る。平坦な環準同型の P による忠実平坦性の保存を、必要な affine 入力で供給する。任意の環の Frobenius 自体の平坦性を仮定しない。
- **G5**：模型と実際の affine conerve の filtered 比較を用い、v 被覆 f に対して `AugmentedRingCechExact (P_* C(f))` を得る。

これらの入口を受ける条件付きの補題だけを最終の v 降下定理として提出しない。G5 が別の表示の複体を出口にする場合も、2g-2 内で増大余単体対象と実際の構造写像への比較を供給する必要がある。

## 3. 型つきの主項目

### H01：完全環の canonical な順極限同型

型案：可換環 A、素数 p、hz、`F = projectivePrimePowerRingHom p hp hz` の全単射性に対し、

```text
ε_A : P(A) ≃+* A
ε_A.toRingHom.comp (frobeniusDirectLimitOf A p hp hz 0) = RingHom.id A
```

第 n 段との式は `ε_A ∘ ι_n = F^{-n}`。順極限の互換条件は `F^{-(n+1)} ∘ F = F^{-n}` で確認する。逆射は第 0 段の構造射。単なる同型の存在でなく、この構造射と対応する同型を選ぶ。

完全環の入口では `PerfectRing` の冪写像の全単射性から hF を供給する。係数準同型 f に対する自然性は

```text
ε_B ∘ P(f) = f ∘ ε_A
```

として示す。これは H01 の法則で、別の主項目に数えない。環の `hz` や素数証明の表示を変えた際の移送も同じ実際の準同型を保持する。

### H02：Frobenius 順極限と増大 Čech conerve の比較

型案：p の像が零の環の射 f:A→B に対して、増大余単体可換環の同型

```text
χ_f : P_* C(f) ≅ C(P(f))
```

を構成する。増大項は P(A)、第 n 項は B の A 上の n+1 重テンソル冪の P と、P(B) の P(A) 上の同じテンソル冪との比較。下記 §7 の照合により、conerve 関手の左随伴性による余極限保存を使う方針に整理した。テンソル冪ごとの対角の終性を新しく実装することは第一案にしない。

必要な可換式は、各テンソル因子の挿入、二因子の積、単位で検証する。これにより余面・余退化・増大との自然性を得る。各次数だけの同型やホモロジーの同型では代用しない。

この比較は普遍性から構成する新規の主項目。既存の `frobeniusRingSequentialColimitIso_naturality` は、環図式から加法的な順極限比較への自然性を与えるが、環のテンソル冪の普遍性まで証明したものではない。ここを既存の結果として数えない。

### H03：完全環の一射の Čech 完全性

型案：p の像が零で冪写像が全単射な A、B、f:A→B、`IsAffineVCover f` に対して

```text
SerrePositivity.Cech.AugmentedRingCechExact C(f)
```

を得る。G5 の `P_* C(f)` の完全性を H02 で `C(P(f))` へ移す。H01 の自然な ε_A、ε_B を実際の Arrow の同型へ組み、conerve の関手性で `C(P(f)) ≅ C(f)` を得て移送する。B1 の `ringCechExact_iff_of_iso` を使う。全正次数の完全性と増大項の単射性をともに移す。

この構成なら「テンソル冪が完全環である」を各次数で個別に仮定する必要はない。テンソル冪の P との比較は H02 から供給される。

### H04：有限族の最終出力

型は §1 の `cech_exact_of_vCover_perfect` そのもの。G0 の `isAffineVCoverFamily_iff_pi` を用いて有限族を `A → ∏ i, B i` にする。積の p 乗写像の全単射性は座標ごとに示し、H03 へ代入する。

空の添字集合も型から除かない。積は零環になり得るので、中間の積へ `CharP _ p` や `Nontrivial` を無条件に要求せず、hz と冪写像の全単射性で扱う。必要なら G0 の非自明な基底上の族の非空性を使って分岐する。有限積の法則や評価写像との可換式は H04 の法則であり、主項目の追加には数えない。

## 4. 既存の部品と照合箇所

| 材料 | 使う所 | 作り直さないもの／未供給の所 |
| --- | --- | --- |
| `FrobeniusDirectLimit.lean`、`FrobeniusDirectLimitMap.lean` | H01、H02 | 有向系、構造射、有限段の一致判定、射の合成・恒等の法則を再利用。H01 の完全環の同型は未実装 |
| `FrobeniusRingSequentialNaturality.lean` | H02 の図式照合 | 環図式の射に自然な既存の加法的比較。テンソル比較は追加で必要 |
| `AffineVCoverFamily.lean` | H04 | 有限族と一射の付値判定の同値は検証済み |
| B1 `Basic.lean` | H03 | `ringCechExact_iff_of_iso`、`ringCechExact_iff_acyclic`。完全性の定義を再定義しない |
| B1 `Filtered.lean` | G5 | `ringCechExact_colimit`、`isCechExact_colimit`。filtered な完全性の一般論は再実装しない |
| B1 `Composition.lean`、`Double.lean`、`BaseChange.lean` | G4 | 消去には合成の完全性だけでなく正次数の底変換の完全性を実際に供給する |
| 2f `projectivePerfectCartesianSquare_acyclic` と辺の比較 | G3・G4 | 射影 Čech 版の入力。一般の固有射の層コホモロジーの有限性や Stein 分解へ範囲を戻さない |
| Mathlib の通常の冪写像・完全環・環の余極限 | H01・H02 | `Perfection` の逆極限を、ここで必要な Frobenius 順極限と取り違えない |

BS17 Lemma 3.4(xii) で使うのは、平坦な射の完全化が平坦であること。これは Frobenius 順極限を平坦加群の filtered 余極限として表す入力であり、「一般の F_p 代数の Frobenius は平坦」とする入力ではない。忠実性は別に全射性の保存と照合する。この affine 入力は G4 の実装時に検証し、2h の未記載の追加仮定へ押し込まない。

## 5. §9 の条件と宇宙

- 中間の射影・形式関数の結果は名前と docstring を Čech 版とする。導来関手の Hⁱ と一致する比較は今回形式化しない、という既存の決定を保つ。
- 共通アフィン細分、底変換、閉厚化、Frobenius、filtered colimit の既存比較は、G4・G5 で実際の射をそろえて使用する。2h はその自然な環図式を最後の同型へ運ぶ。
- 環・族・試験付値環は既存の最終入口と同じ Type u。加群の宇宙を狭める新しい変更は不要。係数環と加群を分けた旧 API の変更を H01〜H04 に便乗して増やさない。
- 出口は §1 の `AugmentedRingCechExact` のまま。H⁰ の層条件だけや、各次数の非自然な同型に弱めない。
- import は AlgebraicGeometry・CommutativeAlgebra・Mathlib・B1 の方向を守り、BS、KST、drafts、∞ 圏から import しない。alias が必要なら `deprecated_alias_util`。

## 6. 規模、検証、開始条件

2h の新規本体と入口・対象検証用の追記の見込み。2g の未完の幾何や G4・G5 は含めない。

| 項目 | 下端 | 上端 |
| --- | ---: | ---: |
| H01 と自然性・段の式 | 400 | 800 |
| H02 と余面・余退化・増大の整合性 | 900 | 2,200 |
| H03 と一射の移送 | 300 | 700 |
| H04 と有限積の法則 | 150 | 400 |
| 登録・型照合・小さい検証の補助 | 250 | 900 |
| 合計 | **2,000** | **5,000** |

H02 の幅は、環の余極限と対角の比較をどれだけ直接既存 API で書けるかに依存する。これは証明前の見積もりであり、2g の残りの見積もりを置き換えない。主項目の法則・証明分割は数を制限しないが、200 行を超えるファイル・補題は実測と型を報告する。

実装する際は H01 → H02 → H03 → H04 の小さい対象ビルド、最後に入口と小さい監査。すべて共有の鍵 `with_build_lock.sh --class impl --wait 3600` を使い、待ちは一つ。main の凍結と B4 の優先を守る。

現在は 2g-1 の C01 による新しい独立構成の境界で止める指示に従い、段 0 の紙だけを記録した。H03 の未完の入口を仮定しただけの定理を完成扱いにしたり、この段 0 を理由に先に Lean 実装を始めたりはしない。

## 7. 停止後の紙の照合：H01・H02 の実装入口

2026-11-14。main は `fb3dfd20e` のままで、確認した正本の停止条件に変更はない。この追記は新しい主項目を追加しない。Lean の編集・検証は行っていない。

2g-1 の一覧：済み 6／全体 12（うち追加 3）

2h の一覧：済み 0／全体 4（うち追加 0）

### H01：零環を含む仮定の直接照合

Mathlib `FieldTheory/Perfect.lean` の `PerfectRing.bijective_frobenius` は、定義上 `Bijective (fun x : A ↦ x ^ p)` を与える。H01 の `projectivePrimePowerRingHom` の全単射性にはこれを直接使える。`ExpChar` を先に立てて通常の `frobenius` との一致を経由する必要はなく、積が零環になる場合にも仮定を増やさず済む。

`Algebra/Colimit/DirectLimit.lean` の `DirectLimit.Ring.lift`、`lift_comp_of`、`hom_ext` を用いれば、逆 Frobenius の n 乗を第 n 段の射とした lift の構造射との式から同型の両逆性と自然性を確認できる。これらの API はソースで確認したが、H01 の Lean の型検査や証明はまだ行っていない。

### H02：左随伴を再利用する経路

Mathlib `AlgebraicTopology/CechNerve.lean` に次の既存の型がある。

```text
CosimplicialObject.augmentedCechConerve :
  Arrow C ⥤ CosimplicialObject.Augmented C
CosimplicialObject.cechConerveAdjunction :
  augmentedCechConerve ⊣ Augmented.toArrow
```

B1 の `Cech/Filtered.lean` の `isCechExact_colimit` は、この左随伴性を `IsLeftAdjoint` に渡して `preservesColimitIso` を使っている。H02 でも同じ一般論を再利用する。

1. f の始域・終域の Frobenius と可換式から `D_f : ℕ ⥤ Arrow CommRingCat` を作る。各対象は f、遷移射の左右の成分は実際の Frobenius の反復。
2. 始域・終域の代数的順極限に `DirectLimit.Ring.lift` の普遍性を入れ、環の圏の余極限と比較する。既存の `ringDirectLimitIntColimitIso` は整数加群の同型なので、環の余極限同型としてそのまま使わない。
3. 左随伴性から `colimit (D_f ⋙ augmentedCechConerve) ≅ C(colimit D_f)` を得る。右辺の矢印を `P(f)` と同定する。
4. 左辺の各遷移が、conerve の各次数の p 乗反復に一致することを示し、`P_* C(f)` と同定する。wide pushout の挿入写像との式で環準同型を一意に決める。この一致を定義的な一致と決めつけず、増大項と全次数で照合する。

この整理で、面・退化・増大の互換性の大部分を関手性と自然同型から受け取れる。第 2・第 4 項の構造射の式が H02 の残る実装内容。独立した「有限テンソル積と filtered 余極限の交換定理」を追加して作る計画にはしない。既存の上端 5,000 行はまだ維持し、実装前のソース照合だけで見積もりを縮めない。
