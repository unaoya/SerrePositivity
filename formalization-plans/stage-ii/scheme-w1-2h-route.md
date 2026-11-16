# SC-W1 2h：段 0（紙）

> 2026-11-17の現在の状況は§12と末尾の承認追記。2g-1とG3は完成、G4・G5は未完。20,000行の境界の後、ユーザーが外枠21,000行への拡張と同じ型・範囲での再開を承認した。2hのLeanの新規実装は未開始。

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

## 8. C02 の境界での紙の追加照合（2026-11-14）

§1〜§7 の C01 未供給・凍結中の記述は各時点の履歴である。現在は C01 と I01〜I04、一般平坦開を伴うアフィン Noether 模型と実際の Spec の図式の比較を検証済み（85507998e）。B4 も完了し、main の凍結は解除された。新しい境界は [C02 候補](scheme-w1-2g-1-fp-envelope-boundary.md) の有限表示の閉包絡の存在構成であり、ここでは Lean の実装を始めない。

2g-1 の一覧：済み 7／全体 12（うち追加 3）。

2h の一覧：済み 0／全体 4（うち追加 0）。

利用側 A6/ArcSheafProperty.lean の cech_exact_of_vCover_perfect と、B1 Cech/Basic.lean の AugmentedRingCechExact・ringCechExact_iff_of_iso をソースで再照合した。B1 の完全性は増大の単射・第 0 次の完全性・全正次数の完全性を同時に持ち、ここを H⁰ の条件だけに替えない。H03 は H01・H02 の環の増大余単体対象の実際の同型を、この既存の同型不変性へ渡す。

H04 の積について、Mathlib.FieldTheory.Perfect の instPerfectRingProd は ExpChar を仮定しているため、零環を含み得る積への入口としてそのまま使わない。各座標の p 乗の全単射性から、関数環の p 乗の単射性は funext と各座標の単射性、全射性は座標ごとの逆像の選択と funext で直接得られる。この法則は空の族でも成り立つ。p の像が零という式も座標ごとに保持し、ProjectiveLocalizedFrobenius.projectivePrimePowerRingHom p hp hz を使うので、積への CharP／ExpChar の追加仮定は不要。

G0 の isAffineVCoverFamily_iff_pi は同じ RingHom.pi f と各 Pi.evalRingHom を使う。H04 の入口をこの既存の橋で一射へ渡し、その後の H01 の自然性も各射影に沿って同じ準同型で読む。利用側にある各 B_i の CharP・PerfectRing の仮定と、最終出力の Arrow.mk (CommRingCat.ofHom (RingHom.pi f)) の形は保つ。この段 0 の主項目を増やさず、2h の見込み 2,000〜5,000 行は維持する。

## 9. C02 判断待ちの追加照合：H02 の環の型と H03 の移送

2026-11-14。main 1ac9c7e37 の指示書の末尾と共通の停止規則を確認した。C02 の承認追記はまだないため、新しい存在構成の Lean は開始していない。この節も紙の照合である。

2g-1 の一覧：済み 7／全体 12（うち追加 3）。

2h の一覧：済み 0／全体 4（うち追加 0）。

### 環値の図式と、既存の加法的な比較を区別する

`FrobeniusRingSequentialDiagram.lean` の `frobeniusRingObjectSystem` は、名前に Ring を含むが型は `J ⥤ ℕ ⥤ ModuleCat ℤ` である。`frobeniusRingDiagram` も `J ⥤ ModuleCat ℤ`、`ringDirectLimitIntColimitIso` も整数加群の同型である。これらをそのまま H02 の可換環の圏の比較として使わない。

環値の実装に使う核は既存の `frobeniusDirectLimitMap`。その値は環準同型で、`frobeniusDirectLimitMap_of`、`_id`、`_comp` が検証済みである。G5 の出口 `P_* C(f)` を可換環値の増大余単体対象として構成する際に、この環の写像を包んだ図式を一度作り、H02 で同じ定義を再利用する。2h のために別の同じ点ごとの完全化を定義しない。G5 が整数加群の表示を途中に使っても、2g-2 の出口の環の増大対象との自然な比較はその段で供給する。

### H02 の Frobenius の一致を示す場所

Mathlib.AlgebraicTopology.CechNerve の実際の定義を照合した。`Arrow.cechConerve.obj n` は `widePushout f.left (fun _ : Fin (n.len + 1) => f.right) (fun _ => f.hom)`。`Arrow.mapCechConerve` は、base の leg では Arrow の左成分、各右因子の leg では右成分を使う `WidePushout.desc` である。

したがって Arrow 上の左右の p 乗準同型から誘導した第 n 項の環の自己射が、同じ環の p 乗準同型に等しいことは `WidePushout.hom_ext` で base の leg と全ての右因子の leg に帰着できる。各 leg では環準同型が p 乗を保つ式を使う。増大項は左成分そのものである。この一致を全余面・余退化ごとに新しく証明するのでなく、conerve の関手性とこの各次数での一致から自然変換の等式としてまとめる。これは未検証の証明案で、各次数の同型だけを完成物として提出しない。

余極限比較は、`CosimplicialObject.cechConerveAdjunction` から左随伴性を供給し、同じ Arrow の逐次図式 D_f に `preservesColimitIso` を適用する。B1 の `isCechExact_colimit` は既にこの実装形式を使っている。環の Arrow の余極限が `P(f)` になることは、始域・終域の環の cocone と `DirectLimit.Ring.lift` の普遍性・構造射との式を示してから同定する。整数加群の同型を根拠に環の積の保存を省略しない。

添字 ℕ の逐次図式を、B1 の同じ宇宙の small index を要求する API に渡す必要が生じた場合は、ULift した添字との同値で運ぶ。既存の B1 の型を変更したり、最終利用側の環の宇宙を狭めたりしない。

### H03 の同型の方向と最終の型

H01 の ε_A:P(A)≅A、ε_B:P(B)≅B とその自然性は、Arrow.isoMk によって `Arrow.mk P(f) ≅ Arrow.mk f` を与える。その conerve の mapIso と H02 の χ_f を合成して `P_* C(f) ≅ C(f)` を得る。G5 が左辺の AugmentedRingCechExact を供給したら、B1 の `ringCechExact_iff_of_iso` の順方向で右辺の同じ述語へ移す。

ここで使う完全性は Basic.lean の定義そのもので、増大の単射・第 0 次・全正次数を含む。比較後に H⁰ だけを取り出す工程は入れない。H04 の有限族の Arrow.mk (CommRingCat.ofHom (RingHom.pi f)) にも同じ比較を使う。H01〜H04 の新しい主項目は追加せず、見込み 2,000〜5,000 行を維持する。Lean の実装・型検査を行ったという主張ではない。


## 10. 2g-2の規模境界での段0の更新（2026-11-16）

[規模境界報告](scheme-w1-2g-2-size-boundary.md) に従う代わりの紙の作業。2g-1とG3は完成、G4・G5は未完。2g-2の外枠を変更せず、2hのLeanの新規実装は始めていない。旧節のG1・G2やH02の未供給は当時の記録で、この節で現状を更新する。

2g-2 の一覧：済み1／全体3（うち追加0）。

2h の一覧：済み1／全体4（うち追加0）。H02相当は2g内の既存の検証済み宣言で供給されたものとして数え、同じ構成を作り直さない。H01・H03・H04は未実装。

### 使う同じ環図式と既存の部品

- **H01（未実装）**：完全環の実際の `FrobeniusDirectLimit` の canonical な ε_A:P(A)≃+*A を、元の第0段の構造射を逆射として作る。型案と自然性は§3のまま。`PerfectRing.bijective_frobenius` と元の `projectivePrimePowerRingHom` の逆反復を `DirectLimit.Ring.lift` へ渡す。零環を扱う一般入口は `(p:A)=0` と p乗写像の全単射性を使い、`Nontrivial` や積への `ExpChar` を足さない。第n段の式と `ε_B.comp P(f)=f.comp ε_A` を同じ元で示す。
- **H02（既存の供給）**：`FrobeniusAugmentedRingCoefficients.lean` の `frobeniusAugmentedRingCoefficients` は各実際の係数環と射の Frobenius 順極限を持つ、可換環値の増大余単体対象。`frobeniusAugmentedRingCoefficientsIso` は、その対象と `Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap ... f.hom.hom)).augmentedCechConerve` の実際の自然同型である。`frobeniusRingConerveIso`、`frobeniusConervePerfectIso_naturality`・`…_augmentation` が全ての単体の射と増大を保持し、`frobeniusConervePerfectIso_arrow_naturality` が元の可換なArrowの射も保つ。これは§3のχ_fの型そのものであり、テンソル冪の比較や環の余極限を2hで再実装しない。`frobeniusRingDiagram` の整数加群の同型だけをこの環の同型として使うものではない。
- **H03（未実装）**：G5から同じ `frobeniusAugmentedRingCoefficients` の `AugmentedRingCechExact` を受け、H02とH01の自然性から作る `Arrow.mk P(f)≅Arrow.mk f` の conerve の同型を合成する。B1の `ringCechExact_iff_of_iso` で同じ増大の単射・第0次・全正次数を移す。元の正次数の各テンソル項の完全環性を別の仮定にしない。**G5のこの入口はまだ未供給で、最終定理の追加仮定として残さない。**
- **H04（未実装）**：G0の `isAffineVCoverFamily_iff_pi` で同じ `RingHom.pi f` の一射へ渡し、有限積のp乗の全単射性とp=0を座標ごとに供給してH03を適用する。空の族も除外しない。`FrobeniusDirectLimitPi` は同じ有限積の順極限の実際の比較と再添字付けの自然性を供給しており、必要な係数移送に再利用できる。最終の族の添字は利用側と同じ Type u・Finite のままにする。

### G5の必要な出口と、既存の模型

G5の要求は、元の `IsAffineVCover f` から、同じ元のArrowの `frobeniusAugmentedRingCoefficients` の `AugmentedRingCechExact` を、模型の存在やNoether性を追加仮定にせず得ること。G4のNoetherな場合の実際の降下は未完である。

忠実平坦なアフィン入力の実際の完全性は `frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat` とB1のfiltered完全性で供給済み。旧§4の完全化による平坦性の話を、未記載の追加仮定としてH03へ足さない。相対 proper fppf の接続は引き続きG4の未完の仕事である。

G2の `coefficientVCoverModelSmallArrowCoconeIsColimit` は、元の環のArrowを実際のfiltered被覆模型の余極限として供給する。`coefficientVCoverModelCechComparison` は同じ模型の conerve 全体と元の conerve の自然同型。これに `frobeniusConervePerfectIso_arrow_naturality`、同じFrobeniusの構造射、B1の `ringCechExact_colimit` を接続するのはG5内の仕事である。2hへ未供給の模型比較を押し込まず、既存の模型や二重複体の判定法も作り直さない。

### 出口・利用側・宇宙の照合

最終型は§1の `cech_exact_of_vCover_perfect` のまま、結論は `SerrePositivity.Cech.AugmentedRingCechExact ((Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve)`。現在の利用側 `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean` の同名の型、`affineFamilyCech`、完全性の定義を読み直した。増大での単射性・第0次の完全性・全正次数の完全性を含み、元の `IsVCoverFamily` の試験付値環と証人をG0と同じ量化で扱う。2h実装時にこの同じ型の小さな照合を行い、draftsを本体へimportしない。

環と有限族・試験付値環の宇宙を狭めない。被覆の有限な幾何的添字を内部でFinへ移す場合も、実際の再添字付けの写像を保持し、最終の Type u の有限族をFinに制限しない。B1や他レーンのAPIの型を変更しない。中間の射影の主張はČech版であることとStacks 30.2.6との関係を明記する既存の§9の決定を保つ。

### 2hの残りの規模と、開始条件

H02の既存の環の自然同型が供給されたため、2hの残りの見込みを更新する。2g-2の未完のG4・G5の作業はこの表に含めない。

| 主項目／仕事 | 下端 | 上端 |
| --- | ---: | ---: |
| H01：ε_A、元の段の式、環の射への自然性 | 400 | 800 |
| H02：既存χ_fの入口への代入・型照合 | 50 | 150 |
| H03：同じ増大環図式の一射への移送 | 120 | 300 |
| H04：同じ有限族の積への橋と最終の型 | 100 | 250 |
| 登録・型照合・小さい対象検証の補助 | 50 | 150 |
| 残り合計 | **720** | **1,650** |

丸めて約800〜1,700行。従来の2,000〜5,000行との差は、H02を2gの検証済み部品として再利用できることによるもので、主張の弱化ではない。H01〜H04の主項目を増減せず、2hの外枠の判断は調整役に残す。2g-2の規模境界の判断とG4・G5の完成の前に、H03の入口を仮定しただけの最終定理や2hのLeanを実装しない。この更新で代わりの紙の作業を完了し、判断を待つ。

2g-2 の一覧：済み1／全体3（うち追加0）。2h の一覧：済み1／全体4（うち追加0）。


## 11. 18,000行の規模境界での段0の更新（2026-11-16）

[18,000行の規模境界報告](scheme-w1-2g-2-size-boundary-18000.md)による代わりの紙の作業。2g-2は15,159行、完成見込み約17,200〜18,800行。数学の先端7b841f924は対象ビルド・小監査済み。G3は済み、G4・G5は未完で、2hのLeanは始めていない。

### 新しい供給と、まだ使えない入口

今回の `DegreeOneProjectiveModel.perfectCechTupleSquareReducedTotal_acyclic` は、実際のF8図式の正次数の定数基底列を除いた核のtotalの完全性。これはH03が要求する元のアフィンv被覆の `frobeniusAugmentedRingCoefficients` の `AugmentedRingCechExact` ではない。核のtotalを元のY側と中心側へ比較し、Noether帰納・アフィンの出口・G5の実際の模型への移送まで済ませる必要がある。H03にこの不足を仮定として足した最終定理は作らない。

H02の供給は§10のまま。`frobeniusAugmentedRingCoefficientsIso` は同じ増大余単体環の自然同型、`frobeniusConervePerfectIso_arrow_naturality` は元のArrowの射への自然性であり、今回の整数加群のtotalの比較と取り違えない。G5とH03は、この同じ環図式を使う。

### 型案・利用側・宇宙

出口は§1の `cech_exact_of_vCover_perfect` のまま。利用側 `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean` の `AugmentedRingCechExact`・`affineFamilyCech`・同名の定理の型と、B1の `SerrePositivity.Cech.AugmentedRingCechExact` を読み直した。いずれも元の積へのArrowの増大での単射・第0次・全正次数の完全性を含み、単にH⁰の主張へ弱めない。ここでは紙の照合であり、draftsの引用のsorryを解消した、または型検査を実行したという主張ではない。

H01の `ε_A : P(A) ≃+* A` と元の環の射への自然性、H02のχ_f、H03の `ringCechExact_iff_of_iso` による同じ増大環図式の移送、H04の `isAffineVCoverFamily_iff_pi` と有限積の橋という型案は§3・§9・§10を維持する。環と有限族・試験付値環の宇宙、空の有限族、零環を除外しない。導来関手の層Hとの比較を新たに作らず、中間の射影補題をČech版と明記する§9の決定も維持する。

### 不足と規模

H01・H03・H04は未実装。H02は2gの既存の供給を再利用する。§10の内訳（H01 400〜800、H02の代入50〜150、H03 120〜300、H04 100〜250、登録等50〜150行）を維持し、2hの残りは約800〜1,700行。2g-2の残り2,000〜3,600行は、この2hの見込みに含めたり移したりしない。

現在は規模境界での紙の更新であり、2g-2完成後の2h実装開始の承認を求めるものではない。境界の判断を待つ間、2gの型・範囲・最終出力を変えたLeanや、2hのLeanを開始しない。

2g-2の一覧：済み1／全体3（うち追加0）。2hの一覧：済み1／全体4（うち追加0）。


§11の後、ユーザーが2g-2の外枠20,000行への拡張と同じ型・範囲での再開を承認した。2g-2のLeanの停止は解除したが、2hのLeanはまだ始めない。§11は規模境界時点の紙として保持する。

## 12. 20,000行の規模境界での段0の更新（2026-11-17）

[20,000行の境界報告](scheme-w1-2g-2-size-boundary-20000.md)による代わりの紙の作業。検証済みの2g-2は17,611行、数学の先端a1ecabce8。G3は完成、G4・G5は未完。八本823行の比較の下書きは未検証で、本体登録・数学のコミットに含めていない。完成見込み19,600〜20,500行に上振れしたため、新しい2gのLeanの追加・修正を止める。2hのLeanは開始していない。

### 前の境界以降の供給と不足

元の任意の環準同型ρ:R→Sへのアフィンの出口は、モジュール `SpecScalarPerfectTupleTotal` の `ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic`（名前空間はSerrePositivity.AlgebraicGeometry）で供給された。元のρの `AugmentedRingCechExact (frobeniusAugmentedRingCoefficients …)` と、同じSpec.map ρの元のタプルtotalの完全性との同値であり、基底の増大写像と全正次数を保つ。Sの標数の零性もρとRの標数から内部で得ている。このモジュール名は配置の表示であって、宣言の名前空間の接頭辞ではない。

同じF8の元のLeftKernel・RightKernelによる条件付き消去と、元の増大totalからY側へのσの鎖写像性も検証済み。しかし元のLeftKernelと増大totalの完全性の同値、中心側のunsigned successorの比較、Noether帰納・相対proper fppf・G5は残る。したがってH03が使う一般のv被覆の完全性はまだ供給されていない。条件付きのF8の仮定をH03に残した最終定理は作らない。

### 型・利用側・宇宙・規模

利用側 `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean` の `AugmentedRingCechExact`、`affineFamilyCech` と `cech_exact_of_vCover_perfect` を再確認した。§1の最終型を維持する。元の有限族の積への増大conerve、増大の単射・第0次・全正次数の完全性を含む。draftsを本体へimportしたり、その未証明の引用を解消したという主張ではない。

H01のε_A:P(A)≃+*Aと自然性、H02の既存の同じ増大環図式のχ_f、H03の `ringCechExact_iff_of_iso`、H04の同じ有限族と一射のv判定の橋をそのまま使う。環・有限族・試験付値環の宇宙、零環、空の有限族を除外しない。層の導来関手Hとの比較は作らず、射影的な中間補題をČech版と明記する§9の方針を保つ。

H02は供給済み、H01・H03・H04は未実装。残りの見込みは§10・§11と同じ約800〜1,700行（H01 400〜800、H02の代入50〜150、H03 120〜300、H04 100〜250、登録等50〜150）。2g-2の不足をこの見込みへ移さない。境界の判断待ちの間、2hのLeanを始めない。

2g-2の一覧：済み1／全体3（うち追加0）。2hの一覧：済み1／全体4（うち追加0）。


§12の後、ユーザーが2g-2の外枠21,000行への拡張と同じ型・範囲での再開を明示的に承認した。2g-2のLeanの停止を解除し、G4・G5を続ける。§12は境界時点の紙として保持する。2hのLeanは開始しない。
