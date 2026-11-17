# 5∞-3a：残りの型つき一覧と20,000行の条件判定（2026-11-16）

一覧：済み 3／全体 6（うち追加 0）。この表の枝番はHT04〜HT06の証明・法則・検査の分割であり、承認項目の追加ではない。HT04〜HT06は全て未完成。

指示：main `cae591fa414d34db6e908369dc3d4b4c9bec9c3c` の `formalization-plans/stage-ii/bulk-5inf3a.md` 末尾の追記。数学の基準は `28763cb06`、直前の報告は `f7b7b44c1`。検証済み157モジュール・13,341行・1,708宣言を固定し、残りの追加分だけを見積もる。この紙の段階ではLean・監査登録・draftsを変更せず、鍵も使わない。

## 1. 記号と対象

以下は実装前の型の仕様であり、未実装の記号がLeanで型検査済みだという主張ではない。

- `D(R)` は既存の `DerivedCategory (ModuleCat R)`、`Q_R` は元の複体の局所化。`H_i` は指定されたホモロジー関手。
- `P₀ = universalOrientedPrism p`、`A₀ = UniversalOrientedPrismRing p`、`h₀ = universalOrientedPrism_bounded p`。
- `B = Construction61.crystallineCoverRing P₀`、`P_B = crystallineCover P₀`、`h_B = crystallineCover_bounded P₀`、`α = crystallineCoverMap P₀`。
- `α(d₀)=p*u` の単位 `u : Bˣ` は既存の `existsUnique_generator_unit` の同じ証人を使う。
- `S_R = complexResolutionFunctor R`、`T_α = Λ_(p,p) ∘ Lα* : D(A₀) → D(B)`。`Λ_(p,p)` は既存の導来主元完備化を二回合成する。
- `F(P) = affineLineFormalModel P`、`K(P,h,r) = affineHTTotalComplex P h r`。`Res_P` は `affineBaseToPolynomialMap P r` による元の基底作用への制限。
- `M(P,h,r) = affineBaseModules P h r`、`X(P,h,r) = coefficientSingleRows M(P,h,r)`。元の係数射は `affineHTCoefficientReducedAny`。
- 任意の有界向き付きprism `P : OrientedPrism p A` への分類射 `g : P₀.Hom P` は、既存の `existsUnique_universalOrientedPrismHom P` で `g(d₀)=P.generator` を満たすもの。`z : Zp →+* A` は既存のp進係数射。
- D30の二つの関手は `b* = T_α ∘ Res_g : D(A) → D(B)`、`c* = T_α ∘ Res_g ∘ Lz* : D(Zp) → D(B)`。導来環Eは構成しない。`Δ̄(P,h,r)` は元の剰余行の積Totの局所化で、`affineBaseSingleTotalPolynomialIso` により元の `K(P,h,r)` の基底への制限に指定同型で戻す。

## 2. 型つきの残作業

### HT04.R1：剰余行の標準比較とTot（旧報告の1）

`X = X(P₀,h₀,1)`、`Y = X(P_B,h_B,1)`、`x = ![(p:A₀),d₀]`、`C = finiteCompletionFunctor (fun j => α(x j))` と置く。

必要な厳密な余単体的複体の射の型：

```text
κ : resolvedCompletedBaseChange α x X ⟶ Y ⋙ C
∀ n : SimplexCategory, QuasiIso (κ.app n)
```

`κ` は元の半自由増大、元の係数射からの線形延長、標準完備化単位に基づく射とする。各項で、その局所化の射が `affineReducedCoverTermIso` の指定同型および終域の完備化単位と一致する式を証明する。余単体射への自然性を構造の一部として証明する。既存の各項の同型の存在だけでは、この射の擬同型性を供給したとしない。

一様下界と元のTotの射への帰結：

```text
QuasiIso (Tot.map κ)
Q_B.obj (Tot (resolvedCompletedBaseChange α x X)) ≅ Q_B.obj (Tot Y)
```

ここで後者は `Tot.map κ` と `Y → Y⋙C` の標準単位から構成する。対象ごとの導来同型を厳密な図式へ持ち上げられるとは仮定しない。像の座標 `α(p), α(d₀)` と `(p,p)` の正規化は、既存の `coverImageCompletionNatIso` の単位の式と照合する。

### HT04.R2：形式模型と元のηの照合（旧報告の2）

既存の `exists_affineLine_HT_realization P₀ h₀` の同じ型の射を使う：

```text
η : F(P₀) ⟶ K(P₀,h₀,1)
(formalZeroIso P₀).hom ≫ H₀(η) = ModuleCat.ofHom (affineHTTotalMap P₀ h₀ 1 0)
(formalOneIso P₀).hom ≫ H₁(η) = ModuleCat.ofHom (affineHTTotalMap P₀ h₀ 1 1)
```

被覆像の形式模型と元の被覆上の形式の指定同型を作り、元のTotの比較と合わせて、次数 `i=0,1` で次の正方形を証明する：

```text
H_i(T_α(Q_A₀.map (Res_P₀.map η))) ≫ e_target_i.hom
  = e_source_i.hom ≫ ModuleCat.ofHom ((u⁻¹)^i • affineBaseHTMap P_B h_B 1 i)
```

`e_source_i` は被覆像の形式模型のホモロジーから、元の `affineForms P_B 1 i` のB基底作用での加群への同型、`e_target_i` はHT04.R1と元のTot・零延長の指定同型から `(affineBaseComplex P_B h_B 1).homology i` への同型とする。右辺の単位はBのスカラー作用であり、一次では `affineBaseToPolynomialMap P_B 1 (u⁻¹)` の作用に等しい。元のBocksteinの式 `β_B∘α*=u·α*∘β₀` を使って向きを確定する。

零次・一次以外についても被覆像の形式模型の消滅を確認し、擬同型性を検査できる型まで戻す。元の形式模型のK-flat性や、任意に選んだηの自然性を追加仮定にしない。

### HT04.R3：普遍向き付き基底の一変数の終点（旧報告の3）

HT03の特定の普遍結晶被覆の標準HT同型とHT04.R1・R2から、次を証明する：

```text
QuasiIso ((completedCoverModelFunctor P₀).map
  ((S_A₀).map (Res_P₀.map η)))
```

その後、既存の `affineLine_moduleComparison_of_resolvedCover` に前提を供給する。HT04の終点は次の型：

```text
Bijective (hodgeTateMapZero P₀ h₀ 1) ∧
Bijective (hodgeTateMapOne P₀ h₀ 1) ∧
∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P₀ h₀ 1 i)
```

普遍基底の正則性・完全平坦性は既存の二つの入力定理を使う。一般の結晶比較をここへ入れない。

### HT05.R1：任意基底へのD30の関手と反映

上記の `b*`, `c*` を既存の導来加群関手で実現し、元の単位・合成と係数作用を照合する。反映の必要な型は、任意の射 `f : K ⟶ L` について：

```text
IsComplete A p K → IsComplete A d K →
IsComplete A p L → IsComplete A d L →
IsIso (b*.map f) → IsIso f
```

`Res_g` の完全性・同型の反映と、元の普遍基底の被覆の反映を合成する。`g(d₀)=d` によるp・d完備性の移送を証明する。`A₀→A` の平坦性・有限Tor振幅、または係数制限後のK-flat性を仮定しない。

### HT05.R2：D30の元の行・Tot・標準写像の比較

元の包の底変換、元の二つの係数脚、テンソルの結合と係数制限を、同じ指定された余単体的模型で比較する。必要な型：

```text
e_r : b*.obj Δ̄(P,hP,r) ≅ c*.obj Δ̄(ZpPrism,h_Zp,r)
```

この同型を元の行の比較と標準単位から構成し、`b*` と `c*` による零次形式・一次形式の像の同型に対して標準ηの正方形を証明する。任意の `A₀→A` にHT02を有限Tor振幅の仮定付きで直接適用しない。Totとの交換は、元の普遍被覆の上界三、Zp側の既存の振幅、係数制限の極限との両立を使う。剰余因子と生成元の単位の式も含める。

### HT05.R3：一般基底の一変数から有限変数の元のηへ

最初にHT05.R1・R2とZpの既存の計算で、任意の `P,hP` に対する公開終点を証明する：

```lean
Function.Bijective (hodgeTateMapZero P hP 1) ∧
Function.Bijective (hodgeTateMapOne P hP 1) ∧
  ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i)
```

次に元の一変数のH²の消滅からBocksteinの平方零を供給し、元の座標外積・完備化単位・cup積の法則とHT05.R2の同じ比較で全有限変数へ戻す。最終の公開型は変更しない：

```lean
(hP : IsBoundedPrism P) (r : ℕ) : HodgeTateIsoStatement P hP r
```

一変数の段階で全次数のηの同型性を前提にしない。

### HT06.R1：一般結晶の系・公開型・検査と昇格

HT05の一般HTの後で、次の公開する系を得る：

```lean
(P : OrientedPrism p A) (hcrys : P.generator = (p : A)) (r : ℕ) :
  HodgeTateIsoStatement P (crystallineBounded p P hcrys) r
```

名前は既存draftの `affineLine_moduleComparison`、`hodgeTate_iso`、`hodgeTate_iso_crystalline` に対応させる。原典との差はdocstringで「一般結晶のCor5.5を一般HTの後の系として回収」と明示する。標準三公理のみの閉包と元の標準写像への依存を監査し、新規ファイルのBS stage II監査への登録、該当drafts/A1の宣言のimportへの置換、対応表・報告を仕上げる。新しい公開終点の対象ビルド・必要な下流の検査を含む。HT06の完成後だけ5∞-7aの段0へ進む。

## 3. 項目別の追加見込み

行数は追加Leanソース（モジュールdocstring、既存構成の法則、証明の分割、監査のLean追加、draftの機械的な追従を含む）。Markdown・JSONの紙の資料、ログ、生成物は含めない。検証済み13,341行は係数2を掛け直さない。素の値は残りの実装の見込みで、各項目の上下端の両方に係数2を掛ける。

| 項目 | 素の追加見込み | 係数2の補正後 | 根拠・主な不確実性 |
|---|---:|---:|---|
| HT04.R1 | 600–1,000 | 1,200–2,000 | 厳密な行比較、各項の元の射との一致、自然性、Totの標準単位。項別同型は完成しているが射との照合は残る。 |
| HT04.R2 | 500–850 | 1,000–1,700 | 形式模型の被覆像、元のηのH₀/H₁の正方形、単位の作用、高次の消滅。 |
| HT04.R3 | 100–200 | 200–400 | 既存の特定の結晶入力と反映の接続、普遍基底の一変数の公開型。 |
| **HT04 小計** | **1,200–2,050** | **2,400–4,100** | 旧報告の未解決1〜3を全て含む。 |
| HT05.R1 | 250–450 | 500–900 | 分類射は既存。係数制限の完備性と反映、二つの古典的関手の接続。 |
| HT05.R2 | 550–1,000 | 1,100–2,000 | 非平坦な任意基底へのD30、二つの脚とTot、剰余因子、元の標準ηの照合。 |
| HT05.R3 | 400–750 | 800–1,500 | 一変数から平方零、有限変数の外積と完備化、元の全次数の標準ηへの帰結。 |
| **HT05 小計** | **1,200–2,200** | **2,400–4,400** | 一般の結晶比較は入力に含めない。 |
| HT06.R1 | 150–300 | 300–600 | 公開する系、監査・登録・該当draftの昇格、必要な検査のLean追加。 |
| **残り合計** | **2,550–4,550** | **5,100–9,100** | 二重計上を避け、法則の分割も各項の見込みに含めた。 |
| **検証済みを足した全体** | **15,891–17,891** | **18,441–22,441** | 固定13,341行＋残りの追加見込み。 |

根拠となる実測：HT01・HT02の完成時の84本・7,935行を固定し、HT03は45本・3,415行、HT04の接続はここまで28本・1,991行。残りHT04.R1・R2とHT05.R2は、これまでに増分を生んだ「元の模型と元の射の照合」に当たる。既存の `affineReducedCoverTermIso` の存在を、未証明の図式の比較の完成として見積もりから除いていない。これらの行数は保証値ではなく、今回求められた係数2による補正前後の見込みである。

## 4. 条件の判定

**補正後の全体上端は22,441行。20,000行を2,441行超える。**

指示の「補正後の全体の上端が20,000行以内なら止まらずにLeanへ、超えるならそこで報告して止まる」に従い、この紙をコミットして停止する。今回Leanの追加・型の変更・一般結晶比較の先取り・ビルド・鍵の取得は行わない。約17,000行の途中報告の条件は保持するが、現在は13,341行のままであり、その点には達していない。

一覧：済み 3／全体 6（うち追加 0）。HT06完成の停止点にも、5∞-7aの開始点にもまだ達していない。
