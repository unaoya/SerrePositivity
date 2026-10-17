# André の平坦性補題の引用解消

## E3：超限反復（2026-10-17）

担当範囲は BS Thm 7.14（著者版 `paper/refs/BS-prisms-author.pdf`、p.61）の
超限反復、極限段の完備性・perfectoid 性・p 完全忠実平坦性、および終段の絶対整閉性。
E3 の作業記録は本節に限る。E1・E2 の節は編集しない。
原典の証明は超限反復を一文で述べており、本レーンの極限段の詳細はその補足である。

### step の仕様訂正（利用者承認済み）

当初指定された型は定数モニック多項式 `1` にも根を要求するため、非零環では不整合。
利用者の回答「正の次数条件を追加する」により、今後は次の型を採用する。
他の引数・宇宙・結論は変更しない。

```lean
step : ∀ (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R),
    (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0
```

既存の `IsAbsolutelyIntegrallyClosed` も正の次数を要求しており、この訂正と一致する。
元の不整合な step から最終定理を導く証明は追加していない。

### E3.1：step に依存しない余極限の部品

配置：`SerrePositivity/BhattScholze/Andre/Transfinite/`。
集約 `Basic.lean` の import をルートに一行だけ追加。

- `isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots`：
  各段の正次数モニック多項式に後の段で根があれば、`Ring.DirectLimit` は絶対整閉。
  有限係数を降ろした後にモニック性と同次数を保つリフトを選ぶ。
  遷移写像の単射性は不要。この結論だけなら可算の塔にも適用できるが、
  **可算塔の後の完備化の絶対整閉性は結論しない**。
- `directLimit_mod_p_pow_surjective`：各段の mod p Frobenius 全射性が有向余極限に保存される。
- `directLimit_mod_p_pow_surjective_of_perfectoid`：全段が perfectoid の場合の適用。
  零環と p ねじれを除外しない。余極限の perfectoid 性はまだ主張しない。
- `exists_stage_countable_family`：添字の任意の可算集合が上界を持つ場合、
  余極限の可算族は一段に同時に持ち上がる。環と塔の添字は Type u に留まる。
  可算族の添字 κ は任意の宇宙でよい。

いずれも step、BS の引用、Cor 8.12、未採用の計画ファイルに依存しない。
既存の Frobenius 判定 `CompatibleRootsPerfectoid.isIntegralPerfectoid_of_compatible_p_roots`
は p 正則性を要求するため、一般の step の極限にそのまま適用しない。
`PerfectoidFrobeniusCriterion.lean` 単独も四条件との同値の完成を主張していない。

検証：`set -o pipefail; lake build SerrePositivity.BhattScholze.Andre.Transfinite.Basic`
が終了コード 0（2510 jobs、最終版に警告なし）。
`lake env lean scripts/audit_andre_e3_transfinite.lean` も終了コード 0。
公開 4 宣言の `assert_no_sorry` と全生成宣言の再帰公理監査を通し、
許可公理は propext・Classical.choice・Quot.sound のみ。
全公開宣言の完全型も同スクリプトの `#print` で確認した。共有ルート全体のビルドは主張しない。

### E3.2：非可算共終性の極限の自動的完備性

`CountableCompletion.lean` と `PerfectoidLimitCompleteness.lean` を追加。

- `isAdicComplete_directLimit_of_countable_upperBound`：任意の可算添字集合に上界があり、
  遷移射が単射で各段が `(p)` 進完備なら、余極限も `(p)` 進完備。
  p は素数でなくてもよい。Cauchy 列だけでなく、その差の p 冪倍表示の証人も
  一つの段に降ろすため、単なる列の持ち上げに依存する不十分な議論を避ける。
  分離性も全ての p 冪に対する割り算の証人を同時に降ろして実証明した。
- `injective_of_perfectoid_completelyFaithfullyFlat`：perfectoid 環からの p 完全忠実平坦な
  写像 φ は単射。作用は φ.toAlgebra。既存の各冪剰余の忠実平坦性と分離性の定理を使用。
- `isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat`：
  可算添字集合に上界がある p 完全忠実平坦な perfectoid 環の有向系の余極限は p 進完備。
  追加の単射性仮定、p 正則性、非零性は不要。環と塔の添字は Type u。

対象集約の `set -o pipefail; lake build` は終了コード 0（3022 jobs）。
新規モジュールに警告なし。既存 `LocalFlatnessCriterion.lean:383` の長行警告のみ再掲。
専用監査は終了コード 0、公開 7 宣言に assert_no_sorry、補助・生成宣言を含む
14 宣言の再帰監査で標準 3 公理のみ。全公開宣言の完全型も #print で確認。
これは非可算共終性の極限での**完備性だけ**の成果であり、perfectoid 性、
極限への完全忠実平坦性、可算共終性の完備化、超限塔の存在は依然未完了。

### 残る範囲

1. 有向余極限の p 進完備化の perfectoid 性（特に p ねじれを許す Fontaine 核の単項性）。
2. p 完全忠実平坦性の有向余極限・完備化・合成による保存。
3. 非可算共終性の可算上界条件を ω₁ 等の具体的順序に供給し、可算共終性の極限で完備化する。
   可算上界条件の下での自動的 p 進完備性は E3.2 で証明済み。
4. Type u に留まる ω₁ までの超限塔の構成、訂正済み step による後続段の供給。
5. 元の Inputs と同じ結論の公開定理、A1 合流による step 解消と再監査。

したがって E3.1 は一般論の部品であり、条件付きの Thm 7.14 自体もまだ証明していない。
`BhattScholze/Inputs/AndreFlatness.lean` は編集していない。

## E1・E2：モニック根付き拡大（2026-10-17）

### 仕様訂正と原典

当初指定の型は `f = 1` にも根を要求するため、`R/p` が非零なら不整合。
ユーザーの明示承認により `(hdeg : ∀ s, 0 < (f s).natDegree)` を `hf` の直後に追加する。
それ以外の引数・宇宙・結論を変更しない。E3 の `Monic ∧ 正次数` という入力とは
二つの引数を組にするだけで接続できる。目標は次の型であり、証明まで宣言しない。

```lean
theorem exists_monicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra;
        IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0
```

原典は BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）。Cor 2.39（p.25）、
Prop 3.13（pp.33–35）、Example 7.9（p.59）の仮定と証明も確認した。
Thm 7.14 は Prop 7.11 を、Rem 7.15 の cover 性は Prop 7.10 を使う。
本レーンはこれらを引用せず、pd 包の明示計算で平坦性を再構成する別経路である。
Rem 7.15 だけで必要な cover 性が証明済みとは扱わない。

### 実装に先立つ一般化設計

| B4-6 の部分 | f の形への依存 | 一般化または再利用 |
| --- | --- | --- |
| `MonicPowerFamilyCover` の expand 基底 | `X_s^n-c_s` の指数の除法に依存 | 一元は `AdjoinRoot` のモニック剰余基底へ。正次数で非空性を確保 |
| `MonicPowerFamilyRelation_isSMulRegular` | 指定変数でのモニック性が本質 | 変数分離と `Monic.isRegular` を任意 f に適用 |
| `DeltaRootAdjoinDivision` の根関係・変数 | `X_s^p-b_s` に固定 | 係数 lift された f を変数で評価し、一般の `DeltaAdjoinDivision` に入力 |
| `DeltaAdjoinDivision` の普遍性・再添字・有限部分族余極限 | 任意元族に一般的 | 型を変えず再利用 |
| `DeltaRootFamilyRaw_p_mul_injective` と先行商正則性 | 冪根関係の冪商表示に依存 | 独立変数の任意モニック商の基底・正則性へ置換 |
| 一般 δ 除算・pd 比較・実導来完備化 | 任意元族と正則性・Tor 入力を受ける部分は一般的 | 仮定と係数作用を個別に照合。`DeltaRoot*` の固定入力から一般性を推論しない |
| `PerfectPrismRootPDPerfectionInputs` 以降 | 補助完備化論は一般的だが公開候補は固定 | 一般定理の入力を供給し `Andre/` に新候補を構成 |
| `exists_rootedPerfectoidExtension_of_perfectPrism` | 元族の p 冪根に限定 | 任意モニック根の存在とは扱わない。perfectoid 商対応と根方程式を保持 |

順序は一元通常根添加 → pd 比較 → 一元 prism 完全化 → 有限独立変数族 →
有限部分族の有向余極限と p 完備化。通常根添加の忠実平坦性だけでその perfectoid 化の
忠実平坦性を結論しない。

### pd 計算の残る証明義務

1. `P = (R/ϖ)[Y^(1/p^∞)]` と `P/(f^p)` の自由基底。有限段のモニック剰余の基底が
   遷移射と両立することが必要であり、自由加群の余極限というだけでは自由性は出ない。
2. Rem 7.15(1) の pd 包の切断多項式表示と、その係数射に関する自由性。
3. Cor 2.39 の仮定を供給した、実 prismatic envelope の Frobenius 引戻しとの比較。
4. 剰余の忠実平坦性と実導来還元の次数集中から p 完全忠実平坦性への移行。
5. 完全化・perfection 後の係数射と根方程式の保持。

一般 perfectoid R には p ねじれがあり得る。候補 T の p ねじれなしを無条件の中間目標に
しない。Rem 7.15 は p ねじれなしへの基底変更を明示しており、元の R への降下は別の義務。

### E1.1：通常モニック商と独立変数の正則性

配置は `Andre/OrdinaryMonicRoot.lean` と `Andre/MonicRelation.lean`。
集約は `Andre/MonicRootedExtension.lean`、専用監査は `scripts/audit_andre_monic_roots.lean`。

- `adjoinRoot_faithfullyFlat`：任意可換環 R の正次数モニック f の `AdjoinRoot f` は忠実平坦。
- `exists_monicRootedFaithfullyFlat`：通常の自由忠実平坦な根付き拡大を同じ宇宙に構成。
- `expandedPower_quotient_free_faithfullyFlat`：正の n,m に対する `f(Z^n)^m` の商は自由忠実平坦。
- `monicRelation_isSMulRegular`：独立変数に評価した任意モニックは非零因子。正次数不要。

既存 B4-6 の対象ビルドは終了コード 0（4299 jobs）。本工程の集約対象ビルドも
`set -o pipefail; lake build SerrePositivity.BhattScholze.Andre.MonicRootedExtension` が
終了コード 0（1999 jobs）。専用監査は公開 5 宣言の `assert_no_sorry` と、
生成宣言を含む対象モジュール全宣言の標準 3 公理限定検査に成功（終了コード 0）。
修正後の最終目標、pd 比較、perfectoid 拡大の忠実平坦性、有限族・任意族の合流は未完成。
通常の自由忠実平坦拡大を E1・E2 完成と数えない。
