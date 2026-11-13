# SC-W1 段 2g：段 0 — v 被覆・被覆模型・Čech 判定法

2026-11-14。停止点 2f の報告 `15753e53f` の直後に作成。これは紙の設計で、以下の新しい名前・構造体・型は **未実装の案**。Lean の検証済み宣言と区別する。main の凍結中も math/scheme だけで文書をコミットする。

**結論：2g は約 16,300〜33,300 行、2h は約 2,000〜5,000 行、残り合計約 18,300〜38,300 行。2g 単独の上端が 20,000 行を超えるので、11-14 の指示に従い、この段 0 の報告で Lean 着手前に止める。** 二重複体の再実装は含めず、B1 と 2d〜2f を再利用した見積もりである。

## 1. 原典の経路と切り分け

[Rydh Thm 3.12](https://davidrydh.se/papers/submersion20100305.pdf#page=15) は、affine または Noether 基底上の有限表示の universally subtrusive な射を、準コンパクトな開被覆と有限表示の固有全射の合成で細分する。3.10 の fppf–proper 細分、準切断、3.11 の準有限な場合を使う。BS17 の v 被覆から universally subtrusive への対応を供給する必要がある。原論文の全ての TIC スキームの一般論を作るかは未決であり、その費用を零と見積もらない。

[BS17 §2](https://arxiv.org/pdf/1507.06490#page=5) の今回の用途は、有限表示の v 被覆の細分、固有全射の帰納的レベル、affine な一般の被覆の有限表示段への近似、降下判定の十分性である。空間値の定理や ∞ 圏は実装せず、加法群の増大 Čech 複体の全次数の完全性へ直接進む。H⁰ の集合値の層条件だけで置き換えない。

[Stacks 0A0P](https://stacks.math.columbia.edu/tag/0A0P) は固有射を有限型 Z 上の固有射の逆極限として表す。今回必要な有限表示モデル・射と等式の有限段への降下は [01ZM](https://stacks.math.columbia.edu/tag/01ZM)、固有性の降下は [081F](https://stacks.math.columbia.edu/tag/081F) に分かれる。標数 p の基底では有限型 F_p のモデルにそろえ、固有性だけでなく全射性・細分の可換図式も同じ段で成立させる。

### 循環を避ける順番

1. affine の付値判定、有限表示の環の射と等式の有限段表示。
2. Rydh の構造定理。非 Noether の入力を単に「Noether モデルがある」と仮定しない。
3. 構造定理の固有全射と有限個の開・射の図式を、同じ有限型 F_p の段へ降ろす。これにより元の有限表示の v 被覆にも被覆の有限段モデルを得る。
4. その Noether な段で被約化と 2d を使い、閉補集合への帰納を始める。
5. 2f の射影四角形と B1 の二重 Čech で完全性を運び、一般の affine 入力には filtered colimit を使う。

Rydh の一般の v 被覆の細分を 2d の固有全射の細分と同一視しない。前者に後者をそのまま代入することはできない。Rydh の全射性／subtrusive 性の有限段への降下も、固有射の全射性の降下だけからは従わない。

## 2. 型の案と界面

以下は Lean に近い仕様記法。未定義の補助名を含むので、本体に仮定付き定理として登録しない。実装では原子となる環準同型・スキームの射・可換式を構成してから束ねる。

### G0：affine の v 被覆

⑥ の入口では、drafts/A6/ArcSheafProperty.lean の `ValuativeCoverFamily (fun _ => True)` と定義的に同じ量化を持つ述語を新設する案。任意の階数の付値環を試す。W の整域構造は同じ存在量化の証人として保持し、環拡大 e は忠実平坦とする。

```lean
-- 案。ι は有限、各 B i と A は CommRing。
def IsAffineVCoverFamily (B : ι → Type u) (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], True →
    ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ True ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k
```

一射と有限積への射の同値、底変換・合成・細分・忠実平坦射・固有全射の判定を作る。付値環への有限積の準同型が一つの因子を選ぶことも実際に証明する。空の族・零環を勝手に除外しない。

BS 側には既に `BhattScholze.Perfectoidization.Derived.IsAffineVCover` があるが、AG から BS を import しない。既存の型は変更せず、利用側で定義を展開した橋を使う。今回の承認は既存型を変える許可ではない。

### G1：Rydh Thm 3.12 の affine 版

```lean
-- f : A →+* B、f.FinitePresentation、上の一射版の v 被覆から：
∃ (T : Scheme.{u}) (q : T ⟶ Spec (CommRingCat.of A))
  (𝒰 : T.OpenCover),
  IsProper q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
  Finite 𝒰.I₀ ∧ (∀ i, IsAffine (𝒰.X i)) ∧
  ∃ k : ∀ i, 𝒰.X i ⟶ Spec (CommRingCat.of B),
    ∀ i, k i ≫ Spec.map (CommRingCat.ofHom f) = 𝒰.f i ≫ q
```

開被覆の全射性は OpenCover のデータで保持する。T の affine 性は要求しない。細分そのものが v 被覆であることは、開被覆・固有全射・合成の保存から証明する。単なる元の Spec(f) の全射性で v 被覆を置き換えない。

### G2：有限型 F_p 上の模型

まず有限表示 affine 射の模型を `Arrow CommRingCat` の filtered 図式で作る案：

```lean
-- hf : IsAffineVCoverFamily B f の一射版
∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
  (D : J ⥤ Arrow CommRingCat.{u}),
  Nonempty (IsColimit (modelCocone D (Arrow.mk (CommRingCat.ofHom f)))) ∧
  (∀ j, FiniteTypeFp p ((D.obj j).left)) ∧
  (∀ j, FiniteTypeFp p ((D.obj j).right)) ∧
  (∀ j, AffineVCover ((D.obj j).hom.hom))
```

`modelCocone` は左右の環の余極限と元の環準同型との可換式を含む実際の cocone の案。`FiniteTypeFp` は p=0 と有限型構造の存在で、証人のない真偽値に模型を隠さない。モデルの v 被覆性を結論で証明し、モデルの存在の仮定に入れない。

固有な証人 q:T→Spec A の降下は別の構造体 `ProperCoverModel` にする案。有限型 F_p 環 A₀、A₀→A、T₀→Spec A₀、有限表示・固有・全射、実際の pullback 比較、有限開被覆と細分の射・等式の降下を同じ証人に保持する。任意の固有射には一つの有限表示モデルと元の T の同型を要求できない。入力が有限表示のときだけ一つの段での同型を返し、一般の固有射は逆極限モデルとして区別する。

全射性は有限表示の構成可能な像と affine 遷移の極限の非空判定を使い、固有性が得られた段より先の共通段へ進める。基底 A₀→A の忠実平坦性は仮定しない。

### G3：Lemma 2.6 の帰納

Noether な有限型 F_p の段で、被約化を有限表示 nilimmersion として許した帰納的レベル `ProperInductiveLevel n f` を定義する案。零段は proper fppf と nilimmersion による細分。正段は proper fppf、射影的 modification、中心の pullback が前のレベルという実際の射の列を保持する。

```lean
-- 有限型 F_p 上、f は有限表示の固有全射：
∃ n : ℕ, ProperInductiveLevel n f
```

帰納は有限 Krull 次元を持つ有限型 F_p の段で始める。任意の Noether 環に有限次元を仮定しない。2d の被約 Noether 基底の出力で稠密開上の同型を得て、閉補集合の次元低下を証明する。nilimmersion の完全性には 2f の nil 不変性を使う。

ブローアップとその有限ファイバー冪を 2f の「有限多項式環上有限な次数付き環の Proj」という入力へ渡すには、有限生成 Rees 環・Segre 表示・irrelevant ideal の標準開条件・構造射の比較が必要。一般の固有射のコホモロジー有限性や Stein 分解は追加しない。

### G4：Thm 2.9 の十分性の複体版

加法群値の前層 P について、`AffineCechDescent P f` は、affine の f の実際の増大 Čech 図式に P を適用した交代複体の全次数の完全性、とする案。中間の非 affine な空間には有限アフィン被覆の複体を使う。

```lean
-- 案。以下の三つは実際の複体・射に関する全称命題として定義する。
theorem affineCechDescent_of_projectiveCriterion
    (P : Schemeᵒᵖ ⥤ AddCommGrpCat.{u})
    (hflat : FppfAffineCechDescent P)
    (hsquare : ProjectiveModificationCechSquaresExact P)
    (hcont : AffineCechFilteredContinuous P)
    (f : A →+* B) (hv : AffineVCover f) :
    AffineCechDescent P f
```

`hsquare` は 2f と同じ、C(X)、C(E)、基底、中心から作る増大全複体の acyclicity。任意の proper modification の四角形を仮定せず、射影版を各ファイバー冪へ適用する。hflat は affine の全ての底変換後の完全性を含む。hcont は単なる対象ごとの同型の存在ではなく、各面・退化・増大写像に自然な比較を含む。

これは界面の型案であり、任意の P への一般化を先に実装することを要求するものではない。BS17 の用途に絞る実装では P を切断環の実際の Frobenius 順極限の加法群に固定して同じ証明を行える。一般化のために新たな仮定を最終出力へ加えない。

注意点：有限被覆を一つずつ選んだだけで、スキームの圏から複体への厳密な関手が得られるとしない。2e〜2f の共通細分と引き戻しの比較を、各有限図式の二重・三重 Čech 図式に入れる。異なる細分の鎖ホモトピーも保持する。単に H の同型を並べて「二重複体が可換」とはしない。この組み立ても G4 の費用に含む。

B1 の `doubleCech_acyclic_iff`、`exact_zero_row_iff_zero_col_of_commute` を使い、第一象限の各対角線が有限な全複体で議論する。合成からの消去 `isCechExact_of_comp` は、合成の完全性に加え正次数の各項への底変換後の完全性を供給して適用する。合成だけの完全性から自動で消去しない。

### G5 と 2h：最終型

2g では実際の環準同型の Frobenius 順極限を各次数へ適用した affine conerve の完全性を出す。2h で完全環の順極限の canonical な環同型、有限テンソル冪、面・退化・増大写像との整合性を証明して元の完全環へ戻す。

```lean
-- 2h の最終仕様。既存の出力と利用側の型は保持する。
theorem cech_exact_of_vCover_perfect
    [CharP A p] [PerfectRing A p]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsAffineVCoverFamily B f) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve
```

drafts の型と定義的に同じ最終出力にする。drafts や BS 本体からの import は追加しない。完全環の入口で必要な Frobenius flatness は Lemma 3.4 の用途に合わせて供給し、任意の F_p 代数の Frobenius が flat と仮定しない。

## 3. 確認した既存の材料と不足

| 場所・宣言 | 再利用できるもの | 不足するもの |
| --- | --- | --- |
| 2d `exists_proper_fppf_blowup_refinement_of_proper_surjective` | 被約 Noether 基底の固有全射の許容 blowup と proper fppf の細分 | 一般の v 被覆から固有全射への細分、nilimmersion、帰納的レベル、有限型段への模型 |
| 2f `projectivePerfectCartesianSquare_acyclic` と `...SquareEdges` | 実際の Cartesian な閉厚化の射影四角形、全複体の完全性、各辺の照合 | 幾何学的 blowup・有限ファイバー冪の Proj 表示、帰納と二重 Čech への代入 |
| 2f `schemeStructurePerfectCommonAffineCechHomologyIso`、`...Pullback_comparison_naturality` | 共通有限被覆、affine 射の実際の引き戻し、Frobenius 係数 | 帰納の有限図式ごとの厳密な二重・三重 Čech の構成 |
| B1 `SerrePositivity.Cech` | `doubleCech_acyclic_iff`、`exact_zero_row_iff_zero_col_of_commute`、`isCechExact_of_comp`、`isCechExact_baseChange`、`isCechExact_baseChange_iff`、`isCechExact_of_retraction`、`isCechExact_colimit` | 幾何学的図式の各入力の証明。二重複体の一般論自体は作り直さない |
| Mathlib `Algebra/Category/Ring/FinitePresentation.lean` | `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`、`...exists_comp_map_eq_of_isColimit`、`CommRingCat.preservesColimit_coyoneda_of_finitePresentation` | 環の有限段表示を有限開被覆・重なり・貼り合わせのスキーム模型へ組む |
| Mathlib `AffineTransitionLimit.lean` | `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`、`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`、`Scheme.exists_isOpenCover_and_isAffine_of_finite`、`nonempty_isColimit_Γ_mapCocone` | 有限表示対象そのものの降下、固有性と全射性の共通段、被覆模型全体 |
| Mathlib `SpreadingOut.lean` | germ-injective な基底上の `spread_out_of_isGermInjective` 等 | 任意の filtered 環の図式への固有射の近似定理ではない。これだけで 0A0P を閉じない |
| Mathlib `ValuativeCriterion.lean`、`RingTheory/Valuation/Extension.lean` | `IsProper.eq_valuativeCriterion`、付値の拡大の材料 | v 判定・subtrusive 性・Rydh の細分を結ぶ一般論 |
| Mathlib `Morphisms/FlatDescent.lean` | 忠実平坦な射による性質の降下 | 今回の A₀→A は忠実平坦とは限らないので、有限段への降下の代用にはならない |

上の不足判定は固定版の Mathlib と現在の math/scheme を `rg` で調べたもの。Rydh の構造定理・v 被覆のモデル構成を完成させた該当 API は確認できなかった。単なる文字検索だけで数学的な不存在を主張するものではなく、実装前には利用箇所ごとに必要な型を照合する。

## 4. 規模と順番

2f の本体・B1・既存 2d を二重計上しない、新規本体と入口の追加の見込み。

| 束 | 下端 | 上端 | 幅の主因 |
| --- | ---: | ---: | --- |
| G0 付値判定と有限族・一射の橋 | 800 | 1,800 | 小さい宇宙の試験環、零環、有限積の因子 |
| G1 Rydh 3.12 の必要な affine 形 | 5,000 | 10,000 | subtrusive 判定、平坦化の適用範囲、準切断・準有限な細分 |
| G2 有限型 F_p の被覆模型 | 5,000 | 9,500 | 有限開被覆の貼り合わせ、固有性・全射性を同じ段で降ろすこと |
| G3 帰納的レベルと射影表示 | 2,000 | 4,500 | nilimmersion、閉中心の次元、Rees・Segre・有限ファイバー冪 |
| G4 Thm 2.9 の Čech 版の十分性 | 2,500 | 5,000 | 共通細分での図式の整合性と B1 の具体的入力 |
| G5 filtered 移送・登録・検証 | 1,000 | 2,500 | affine conerve の各構造写像と余極限の比較 |
| **2g 合計** | **16,300** | **33,300** | |
| **2h** | **2,000** | **5,000** | 完全環、有限積・テンソル冪、最終型への移送 |
| **2h までの残り合計** | **18,300** | **38,300** | |

2d 報告時の 2g 約 10,000〜35,000 行から、今回は残る幾何学的接続を分けて下端を上げた。B1 の利用は以前から見積もりに織り込み済みで、それを理由に再度大きく値引きしない。2f の実測 15,780 行のうち、固定した代数複体から実際の幾何学的図式への接続に相応の費用がかかったことも考慮した。

## 5. 判断が要る点と縮小案

11-14 の着手条件の上端 20,000 行を超えるため、**G0 を含む 2g の Lean は未着手で止める**。これは数学的な反例や不可能性の報告ではなく、規模の条件に達した報告である。2f の検証済み数学・登録・報告は全てコミット済み。

判断案は、現行範囲の G0〜G5 をこの見積もりで進めるか、幾何学的供給の G1〜G2 と、B1 を使う G3〜G5 を別の段に分けて検収するか。分ける場合も「模型や細分が存在する」という追加仮定を最終の v 降下定理に残さない。

BS17 の用途だけなら、Rydh 3.12 の開被覆まで強めず 3.10 の fppf–proper 細分で降下の消去を進める案もある。ただし現行指示は 3.12 を含むので、これは未承認の範囲変更案である。準切断・準有限な細分の一部を約 1,500〜3,000 行省く可能性はあるが、G2 の模型構成は残り、上端 20,000 行内に収まる根拠にはならない。

有限型 F_p の Noether 入力だけに最終出力を制限すれば G2 の一部を後回しにできるが、既存利用側は任意の完全環であり、その制限は最終型を狭める。採用しない。一般の固有射のコホモロジー有限性・Stein 分解・導来関手との比較を足しても今回の幾何学的不足の解決にはならないため、追加しない。

B3 の main への取り込みと B4 の追従は調整役の手順を待つ。今回は SchemePowerBlowup・SchemeCompositionDomination の属性の対象宣言を変更していない。


## 2026-11-14 の承認後の追記

調整役の新しい指示により、G0 の Lean 着手は承認された。前記の「G0 を含む Lean は未着手で止める」は段 0 提出時点の記録。G1 以降は、3.10 経路との比較を受けた経路・外枠の決定を待つ。停止点を 2g-1（G1・G2）と 2g-2（G3〜G5）に分ける。

G0 最初の区切りは数学 `ed170c16c`、六モジュール・本体 314 行、入口込み 326 行。対象 4,786 jobs 成功、標準監査 10,661 宣言・標準三公理のみ。[G0 報告](scheme-w1-2g-g0-report.md) と [型つき一覧](scheme-w1-2g-g0-types.md) に到達点を記録した。これは 2g-1 の完成報告ではない。

[Rydh 経路の比較](scheme-w1-2g-rydh-route-comparison.md) は同じ最終型を保つ 3.10 経路を提案する。G1 の準切断・open–finite 細分は省けるが G2 の模型は残るため、2g 全体の見込みは約 15,500〜32,300 行。G1 以降の Lean は未着手。型つき一覧の法則・証明分割に本数制限を置かない 11-14 の規則も反映した。


### 3.10 経路の承認後

G0 の付値環拡大、nil な商、忠実平坦射、スキーム側の固有全射の判定と合成・底変換を追加した（数学 `5fb95d17b`・`d902118ed`）。G0 累計本体 682 行、入口込み 710 行。入口 4,796 jobs 成功、標準監査 10,676 宣言・標準三公理のみ。G1 の最初の型つき一覧は [2g-1 記録](scheme-w1-2g-1-report.md)。2g-1 の外枠 25,000 行、約 12,000 行で途中報告し、完成時は報告して G3 へ進む。
