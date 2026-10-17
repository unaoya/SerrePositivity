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

### E3.3：Type u 内の ω₁ と終段

`OmegaOne.lean` を追加。添字は `Ordinal.ToType (ω₁ : Ordinal.{u}) : Type u`。

- `omegaOneIndex_nonempty`、`omegaOneIndex_noMaxOrder`：非空性と真の後続段の存在。
- `omegaOneIndex_countable_upperBound`：任意の可算添字集合に同じ型の上界がある。
  可算個の可算順序数の上限が ω₁ 未満という Mathlib の定理を使う。
- `omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed`：実際の ω₁ 添字の塔に対し、
  全段が perfectoid、全遷移が p 完全忠実平坦、各段の正次数モニック多項式がその後続段に
  根を持つことから、余極限の p 進完備性と絶対整閉性を結論する。
  可算上界条件を追加仮定として残していない。環も添字も Type u。

対象 build 終了コード 0（3023 jobs、新規モジュールの警告なし）。
専用監査終了コード 0、全公開 11 宣言の assert_no_sorry と全 18 宣言の再帰公理監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
この定理は**与えられた塔についての二つの性質**であり、塔の存在、終段の perfectoid 性、
基底から終段への p 完全忠実平坦性は結論していない。Thm 7.14 の条件付き完成とは数えない。

### E3.4：完全平坦性と通常の忠実平坦性の余極限保存

`CompleteFlatColimit.lean` と `FaithfullyFlatColimit.lean` を追加。

- `isCompletelyFlat_colimit`：固定基底の I 完全平坦加群の、正確な余極限は I 完全平坦。
  試験加群を固定した Tor の対称性と既存の正確な余極限保存を使う。
- `isCompletelyFlat_moduleDirectLimit`、`isCompletelyFlat_directLimit`：
  標準加群余極限と非交和モデルに適用。
- `isCompletelyFlat_algebraDirectLimit`：固定基底の代数の有向系にも、元の作用で適用。
  遷移射の束が AlgHom と LinearMap で異なるため、普遍写像から実際の線形同型を構成した。
  作用の定義的同一性だけで移送しない。
- `directLimit_mem_ideal_smul`：基底イデアル倍の表示を一段へ降ろす。
- `faithfullyFlat_algebraDirectLimit`：固定基底上忠実平坦な代数の有向余極限は忠実平坦。
  単位元が基底イデアルの拡張に入る関係を有限段へ降ろす。
  遷移射が単位元を保つことが必要であり、任意の加群の有向系には一般化しない。

いずれも単射性・p 正則性・Noether 性を追加していない。
集約対象 build 終了コード 0（3217 jobs、新規モジュールの警告なし）。
既存の LocalFlatnessCriterion・CompletelyFlatEquiv・DerivedTensorPentagon の警告のみ再掲。
専用監査終了コード 0、全公開 17 宣言の assert_no_sorry と全 37 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型は同監査の #print 出力で検査した。

**残る接続：** p 完全忠実平坦性の余極限保存全体には、剰余テンソル代数の有向余極限と
元の余極限の剰余テンソルとの同型が必要。この接続と、完備化による完全忠実平坦性の保存は未実装。
通常の忠実平坦性の保存を、この二つの証明の代わりにはしない。

### E3.5：剰余比較と I 完全忠実平坦性の余極限保存

`ResidueTensorColimit.lean` を追加。

- `algebraModuleDiagram`、`algebraModuleCocone`、`algebraModuleIsColimit`：
  代数の非交和余極限は元の係数作用を保つ加群余極限でもある。
- `residueTransition`、`residueDirectedSystem`：各段の拡張イデアルによる環商の実有向系。
  標準の R/I 作用を持ち、環準同型として単位元を保つ。
- `residueDiagramIso`：元の加群図式の剰余スカラー拡大と、剰余環図式の自然同型。
  既存の quotientAlgebraScalarExtensionEquiv の自然性を利用した。
- `residueTensorDirectLimitEquiv`：元の余極限 L に対し、
  `(R/I) ⊗[R] L` と各段の通常剰余環の余極限を **R/I 上線形**に比較。
- `isCompletelyFaithfullyFlat_algebraDirectLimit`：固定基底 R 上 I 完全忠実平坦な
  代数の有向余極限 L は、同じ R 作用に関して I 完全忠実平坦。
  I は任意。p 正則性・単射性・Noether 性・I の有限生成性を要求しない。

対象 build 終了コード 0（3219 jobs、新規モジュールの警告なし）。
専用監査終了コード 0、公開全 25 宣言の assert_no_sorry と全 73 宣言の再帰公理監査に成功。
許可公理は propext・Classical.choice・Quot.sound のみ。全公開宣言の完全型を #print で確認。
E3.4 の剰余比較の未接続点は本工程で解消した。

これは **完備化前の有向余極限** の保存であり、p 進完備化による完全忠実平坦性、
合成による保存、極限段の perfectoid 性、超限塔の存在はまだ別の義務として残る。

### E3.6：完全平坦性・完全忠実平坦性の合成

`Composition.lean` を追加。

- `isCompletelyFlat_comp`：I 完全平坦な φ と I.map φ 完全平坦な ψ の合成は I 完全平坦。
  Tor の底変換比較を、元の試験加群の非輪状性と拡大後のイデアル零作用から適用する。
  合成準同型の作用と二段階のスカラー制限を恒等写像の線形同型で比較する。
- `subsingleton_of_annihilated_of_residueTensor`：I で消える任意の試験加群の零性を、
  通常剰余テンソルの忠実平坦性から反映する。係数加群自体の平坦性は不要。
- `isCompletelyFaithfullyFlat_comp`：同じイデアルの配置で完全忠実平坦性が合成される。
  忠実性は拡大した試験加群を二段階で反映し、剰余商の作用を弱めず検証する。
- `isCompletelyFaithfullyFlat_natCast_comp`：p に関する両写像の仮定をそれぞれ
  `letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) B` と
  `letI := ψ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) C` の型で受け取る。
  結論も元の合成準同型の toAlgebra に関する (p) 完全忠実平坦性。p の素数性は不要。

対象 build 終了コード 0（3225 jobs、新規モジュールの警告なし）。
専用監査終了コード 0、公開全 29 宣言の assert_no_sorry と全 78 宣言の再帰監査に成功。
標準 3 公理のみ、全公開宣言の完全型も #print で確認した。
既存の E3 私有補助 3 箇所の docstring も概要／方針／規約／使われ方の形式に統一した。
これで完全忠実平坦性の**合成と有向余極限**の保存を供給したが、完備化による保存は未完了。

### E3.7：未完備余極限の Frobenius 核と完備化のねじれ境界

`TorsionBound.lean` と `FrobeniusKernelColimit.lean` を追加。

- `isReduced_ringDirectLimit`、`isReduced_ringDirectLimit_of_perfectoid`：
  被約環、特に perfectoid 環の有向余極限は被約。遷移写像の単射性は不要。
- `mul_eq_zero_of_pow_mul_eq_zero_of_reduced`：被約環で a^n*x=0 なら a*x=0。
- `ringDirectLimit_p_power_torsion_bound_of_perfectoid`：未完備余極限の p 冪ねじれは p で消える。
- `adicCompletion_power_torsion_bound`：元環の a 冪ねじれが共通指数 N で消えれば、
  (a) 進完備化の a 冪ねじれも同じ N で消える。第 k+m 座標で元の境界を使って実証明した。
- `adicCompletion_ringDirectLimit_p_power_torsion_bound_of_perfectoid`：
  perfectoid 塔の有向余極限を p 進完備化しても p 冪ねじれは p で消える。
  完備化の被約性や perfectoid 性はこの結論に含めない。
- `ringDirectLimit_frobenius_kernel_of_stage_root`、`ringDirectLimit_pow_mem_span_iff_of_stage_root`：
  一段の p=u*π^p を満たす π の像について、未完備余極限でも x^p∈(π^p) ⇔ x∈(π)。
  割り算の証人と等式を共通の後の段へ移し、その段の既存 perfectoid Frobenius 核定理を使用。
- `ringDirectLimit_exists_frobenius_root_data`：未完備余極限に具体的な π と単元 u を選び、
  p=u*π^p、mod p Frobenius 全射性、上記の核表示を同時に供給する。

対象 build 終了コード 0（3497 jobs、新規モジュールの警告なし）。
専用監査終了コード 0、全公開 38 宣言の assert_no_sorry と全 97 宣言の再帰監査に成功。
標準 3 公理のみ、全公開宣言の完全型も #print で確認。

これらは原典 p.61 の一文に対する極限操作の補足証明である。
**未解消：** 完備化後の Frobenius 核表示への移送、p ねじれを許す Fontaine 核単項性の逆判定、
完備化による完全忠実平坦性、可算極限段の構成はまだ必要。
元環・完備化の有界ねじれの証明を、通常／導来完備化の比較の証明の代用にはしない。

### E3.8：完全 δ 表示からの通常完備化の perfectoid 性

`PrismaticCompletion.lean` と `PerfectDeltaColimit.lean` を追加。

- `isIntegralPerfectoid_adicCompletion_of_distinguished_kernel`：
  完全 δ 環 A の distinguished 元 d と、全射 q:A→T、ker q=(d) が与えられれば、
  T の通常の p 進完備化は perfectoid。T の p 正則性・被約性・有界ねじれ・完備性は不要。
  BS Thm 3.10（著者版 p.32）について既に証明済みの完全 prism の商の perfectoid 性を使用。
- `deltaDirectLimit_isPerfect`：完全 δ 環の δ 図式の環余極限上の既存 δ 構造は完全。
  各段の Frobenius 同型を環余極限に移し、その写像が既存の Frobenius 持上げと一致すると示した。
  添字の非空性・有向性や遷移射の単射性を追加しない。

**原典・経路の記録：** BS Lemma 3.9（著者版 pp.31–32）と Thm 3.10（p.32）、
Thm 7.14（p.61）の極限操作の補足として、既存の実 PD 完備化で得た完全 prism の商 Q を用いる。
通常の p 進完備化 C と Q の間の二つの環準同型を、通常完備化と実 PD 完備化の普遍性から作り、
合成が恒等であることをそれぞれの普遍性で検証した。
通常完備化と実導来完備化を無条件に同一視する議論は使わない。
一般の Fontaine 核の逆判定を新仮定にはせず、**raw 余極限の完全 δ 表示を構成する経路**を採る。
E3.7 の Frobenius 条件の保存は独立に証明済みの部品として保持する。

対象 build 終了コード 0（3500 jobs、新規モジュールの警告なし）。
専用監査終了コード 0、公開全 40 宣言の assert_no_sorry と全 99 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認した。

保存時の検証済みソース SHA256：`PrismaticCompletion.lean` は
`f823abb5d79e3ec56990b994b50402b5c0ff161dfbae80e18967b34e27fe7e45`、
`PerfectDeltaColimit.lean` は
`e8dcb7e64a9b003873d680cf3697f5576f1ebbc4816da8c52a73af920568016e`。

**未完了：** perfectoid 塔の Fontaine 環の遷移射・自然性、固定した distinguished 生成元の移送、
raw 余極限での全射と単項核の同定を供給し、上記の一般定理を実際の塔に適用する段階。
この表示の仮定を最終定理に追加して完成とすることはしない。

### 残る範囲

1. perfectoid 塔の raw 余極限の完全 δ 表示を構成し、E3.8 を適用して p 進完備化の perfectoid 性を得る。
2. p 完全忠実平坦性の完備化による保存。有向余極限と合成による保存は E3.5・E3.6 で証明済み。
3. 可算共終性の極限での完備化。ω₁ の可算上界条件と終段の自動的 p 進完備性は E3.2・E3.3 で証明済み。
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

### E1.2：任意関係族の具体的な perfectoid 根候補

`DivisionPerfectoidCandidate.lean` は一般の δ 環・distinguished d・任意元族 a に対し、
δ 除算の p 進完備完全化と実 (p,d) 完備化から完全 prism を構成する。
その商は perfectoid で、元の係数射は d と全 a を零に送る。
`PolynomialPerfectoidCandidate.lean` は a を独立変数に評価した多項式族に特殊化し、
同じ係数射に関する根方程式を証明する。
`PerfectPrismMonicCandidate.lean` は完全 prism の商上のモニック族を同次数モニックに
lift する。この選択は公開定義 `perfectPrismMonicLift` で固定した。

公開定理 `exists_monicRootedPerfectoidCandidate_of_perfectPrism` の正確な出力は
`∃ T, ∃ (_ : CommRing T), ∃ (φ : R →+* T), ∃ (ρ : σ → T),
 IsIntegralPerfectoid T p ∧ ∀ s, (f s).eval₂ φ (ρ s) = 0`。
前提は `P : OrientedPrism p A`、`P.deltaStructure.IsPerfect`、
`R = A/(P.generator)`、同一宇宙の族 f とそのモニック性。正次数はこの候補構成では不要。
この定理は零候補を排除せず、p 完全忠実平坦性の仮定も結論も持たない。
したがって最終目標の代替・条件付き完成とは数えない。

集約の対象ビルドは `set -o pipefail` 付きで終了コード 0（3266 jobs）。
専用監査は新規公開宣言すべての `assert_no_sorry` と、生成宣言を含む 57 宣言の
標準 3 公理限定検査に成功（終了コード 0）。

### E1.3：分冪表示環の実 p 乗商上の自由性とモニック有限段

新規 `Andre/PrincipalDPFree.lean` で、標数 p の任意の B と y に対し
`principalDPPresentation_quotient_free` を証明した。正確な結論は
`letI := principalDPQuotientAlgebra hprime.pos hp y;
 Module.Free (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y)`。
前提は `p.Prime` と `(p : B) = 0` で、y の非零因子性は不要。
既存の切断多項式環上の自由基底を実評価商へ移し、指定された係数射を保っている。

新規 `Andre/MonicPDFlat.lean` の公開結果：

- `monicDPPresentation_free`：標数 p の R とモニック f に対し
  `Module.Free R (PrincipalDPPresentation R[X] f)`。正次数不要。
- `monicDPPresentation_faithfullyFlat`：さらに `0 < f.natDegree` なら
  `Module.FaithfullyFlat R (PrincipalDPPresentation R[X] f)`。
- `expandedMonicDPPresentation_faithfullyFlat`：正の n による f(Z^n) にも同じ忠実平坦性。
- `principalDPPresentation_faithfullyFlat_of_quotient`：一般の基底 R → B について、
  `B/(y^p)` の R 上の忠実平坦性から表示環の R 上の忠実平坦性を合成する。

いずれも Rem 7.15(1)（著者版 p.62）の通常代数の計算。実 prismatic envelope の
Frobenius 引戻しとの同定、無限 p 冪根変数の基底、有向余極限と完備化後の忠実平坦性は
未完成であり、E1・E2 完成とは数えない。
集約の対象ビルドは `set -o pipefail` 付きで終了コード 0（3327 jobs）。
専用監査は全公開宣言の `assert_no_sorry` と生成宣言を含む 63 宣言の
標準 3 公理限定検査に成功（終了コード 0）。

### 保存時の共有インデックス事故

E1.2 のコミット `ba07c9b6` に、同時にステージされた別レーンの
`DifferentialGraded/Endomorphism/ActualScalarEvaluation.lean`、
`ChecksActualScalarEvaluation.lean`、`Compatibility.lean`、
`formalization-plans/dg-theory-u14.md` が混入した。これらは本レーンの成果・検証対象に数えない。
当該レーン側の記録コミットは `eaf5b4ff`。amend・rebase・reset は行っていない。
以降は自分の検証済みパスを `git commit --only` で明示する。

### E1.4：係数商の正則性と一元 raw φ/p 包の p 正則性

`Andre/MonicRelationResidue.lean` の
`monicRelation_coefficientQuotient_isSMulRegular` は任意係数イデアル I に対し、
`MvPolynomial σ R / I.map C` 内の f(X_s) の像が非零因子であることを証明する。
前提は任意可換環 R と f のモニック性だけ。`monicRelation_modP_isSMulRegular` は
実際の `Ideal.span {(p : MvPolynomial σ R)}` による商での同じ正則性。
`monicRelation_map` は任意係数射とこの評価関係式の可換性を与える。

`Andre/MonicRawPDivision.lean` の `monicRawPDivision_p_mul_injective` は、
p 正則な δ 環 A、distinguished な `(p : A)`、モニック f と独立変数 s に対し、
`B = MvPolynomial τ A`、`E = polynomialRankOneDeltaStructure τ D`、`y = f(X_s)` の
`DeltaAdjoinDivision E (p : B) (fun _ : PUnit.{u+1} => E.frobeniusLift y)` で
p の乗法が単射であることを証明する。ghost 単射は G4 から内部で供給する。
`perfectPrismMonicRawPDivision_p_mul_injective` は完全 prism とその δ 完全性から
同じ入力をすべて供給する。正次数はこの p 正則性には不要。

これは Cor 2.39（著者版 p.25）の一元補助 φ/p 計算であり、最終候補の f/d 包の
p 完全忠実平坦性を証明したものではない。
集約対象ビルドは `set -o pipefail` 付きで終了コード 0（3984 jobs）。
専用監査は全公開宣言の `assert_no_sorry` と生成宣言を含む 71 宣言の
標準 3 公理限定検査に成功（終了コード 0）。

### E1.5：先行モニック関係の冪商と任意族 raw φ/p 包の p 正則性

新規ファイルはすべて本レーンの `Andre/` 直下：
`MonicFamilyPartialQuotient.lean`、`MonicFamilySubsetRegular.lean`、
`MonicFamilyPowerResidue.lean`、`MonicFamilyRawRegular.lean`。
B4-6 で `X_s^p-b_s` に固定されていた先行商の正則性を任意の一変数多項式族に一般化した。
変数分割と係数商の交換同型で実商を比較し、任意先行族の p 乗商での後続モニックの正則性を得た。

主要公開定理の正確な型は、`P = MvPolynomial σ A`、
`E = polynomialRankOneDeltaStructure σ D`、`r s = monicRelation (f s) s` とおくと：

```lean
monicFamilyRaw_p_mul_injective
    (D : DeltaStructure p A) (f : σ → Polynomial A)
    (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P)
      (fun s : σ => DeltaStructure.frobeniusLift E (r s)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun s : σ => DeltaStructure.frobeniusLift E (r s))) * x)
```

共通の前提は `p : ℕ`、`[Fact p.Prime]`、`[CommRing A]`。
`A : Type u` と `σ : Type v` を許す。正次数・族の有限性・ghost 単射を追加仮定にしない。
有限部分族について `monicFiniteRaw_p_mul_injective` を、一入力追加の帰納で証明し、
既存の有限部分族余極限 `deltaAdjoinDivisionFamily_p_mul_injective` で任意族へ移した。
ghost 単射は各段の p 正則性と相対自由源の自由性から G4 により内部供給する。

`perfectPrismMonicFamilyRaw_p_mul_injective` は `P₀ : OrientedPrism p A` と
`hP : P₀.deltaStructure.IsPerfect` の下、`D = P₀.deltaStructure` として同じ結論を与える。
係数環の p 正則性と δ(p) の単元性を完全 prism から供給するため、上記 hpA・hdp は引数にない。
これは Cor 2.39（著者版 p.25）の補助 φ/p 計算であり、Rem 7.15（p.62）に向けた準備。
最終候補の f/d 包の忠実平坦性、実 prismatic envelope の Frobenius 引戻しとの同定、
通常モニック族商の自由基底と完備化後の p 完全忠実平坦性は引き続き未完成。
本結果を目標 `exists_monicRootedPerfectoidExtension` の完成と数えない。

集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4001 jobs）。
専用監査も終了コード 0。全新規公開宣言の `assert_no_sorry` と、生成宣言・私有補助を含む
132 宣言の標準 3 公理限定検査に成功した。新規 sorry・axiom・引用は追加していない。

### E1.6：有限モニック族の通常商の自由性・忠実平坦性

新規 `Andre/MonicFamilyQuotientUniversal.lean` は、実関係イデアルによる通常商
`PolynomialFamilyQuotient f` の根方程式、任意の係数射と指定根への普遍射、係数・根による
環射の外延性を構成する。モニック性はこの普遍性には不要。
`MonicFamilyOptionQuotient.lean` の `polynomialFamilyOptionEquiv` は正確に
`PolynomialFamilyQuotient f ≃ₐ[R]
 AdjoinRoot ((f none).map (algebraMap R
   (PolynomialFamilyQuotient (fun s : σ => f (some s)))))` を与える。
これは元の R 係数作用を保つ代数同型で、両方向の普遍射を係数と根上で比較して証明した。
`MonicFamilyQuotientReindex.lean` は添字同値による再添字付けの代数同型を構成する。

`Andre/MonicFiniteFamilyFlat.lean` の主要公開型：

```lean
theorem monicFiniteFamilyQuotient_free_faithfullyFlat
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.Free R (PolynomialFamilyQuotient f) ∧
      Module.FaithfullyFlat R (PolynomialFamilyQuotient f)
```

非零係数環の場合、空集合・Option 帰納で自由性と非零性を同時に証明する。
正次数とモニック性は各段の係数変更後も非零の一元根添加となることに用いる。
零係数環の場合も加群の自明性から処理する。
同じ宇宙の有限 σ について `exists_finiteMonicRootedFaithfullyFlat` は
`∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
 (letI := φ.toAlgebra; Module.Free R T ∧ Module.FaithfullyFlat R T) ∧
 ∀ s, (f s).eval₂ φ (ρ s) = 0` を与える。

BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の通常代数の準備。
Prop 7.11 を使う原典の証明とは異なる、明示的なモニック剰余と普遍射による計算である。
任意族の余極限、分冪包の実導来比較、最終 perfectoid 候補の p 完全忠実平坦性は未完成。
通常の有限自由忠実平坦拡大を目標定理の完成と数えない。
集約の対象ビルドは `set -o pipefail` 付きで終了コード 0（4005 jobs）。
専用監査は全新規公開宣言の `assert_no_sorry` と、生成宣言を含む 176 宣言の
標準 3 公理限定検査に成功（終了コード 0）。

### E1.7：有限部分族余極限と任意モニック族の通常忠実平坦性

新規 `Andre/MonicFamilyFiniteSystem.lean` は、固定した族 f の有限部分族に対する
実通常関係商 `PolynomialFamilyFiniteStage f T` と、包含に沿う標準 R 代数射を構成する。
各射は元の係数と指定根を保ち、恒等・合成則を満たす。
`Andre/MonicFamilyColimit.lean` の `polynomialFamilyColimitEquiv` は
`PolynomialFamilyColimit f ≃ₐ[R] PolynomialFamilyQuotient f` を与える。
各根を一元部分族の段から余極限に写して逆射を作り、各有限段と全族の標準根で相互逆性を証明した。
この代数同型にはモニック性・正次数・遷移射の単射性を仮定しない。

`Andre/MonicFamilyFaithfullyFlat.lean` の主要公開型：

```lean
theorem polynomialFamilyQuotient_faithfullyFlat
    {R σ : Type u} [CommRing R]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat R (PolynomialFamilyQuotient f)
```

`exists_familyMonicRootedFaithfullyFlat` の結論は正確に
`∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
 (letI := φ.toAlgebra; Module.FaithfullyFlat R T) ∧
 ∀ s, (f s).eval₂ φ (ρ s) = 0`。
同じモニック性・正次数だけを仮定し、任意濃度の族と零係数環を許す。

有限段の忠実平坦性は E1.6 による。余極限の通常忠実平坦性は A2 の既存成果
`Transfinite.faithfullyFlat_algebraDirectLimit` を直接再利用した。
依存対象 `Andre.Transfinite.FaithfullyFlatColimit` の対象ビルドは終了コード 0（2052 jobs）。
全族の実商への移送では元の係数作用を保つ上記の R 代数同型を使う。
自由加群の余極限であることから自由性を推論していない。

BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の通常同時根添加の部分であり、
Prop 7.11 を使う原典と異なる有限部分族の明示商による経路。
これにより通常の根族商の忠実平坦性は任意族まで得られたが、分冪包・prismatic envelope の
実導来比較、無限 p 冪根変数の自由基底、最終 perfectoid 候補の p 完全忠実平坦性は未完成。
`exists_monicRootedPerfectoidExtension` は依然未宣言で、通常拡大を目標の完成と数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4009 jobs）。
専用監査も終了コード 0。全新規公開宣言の `assert_no_sorry` と、生成宣言を含む
221 宣言の標準 3 公理限定検査に成功した。再利用する A2 の通常忠実平坦余極限定理も
明示的な `assert_no_sorry` の対象に加えた。

### E1.8：任意モニック族の補助 raw φ/p 包の p 完全忠実平坦性

新規 `Andre/MonicFamilyCoefficientQuotient.lean` は、全族のモニック関係商と係数商の
交換を、係数と各多項式の代表元を保つ実環同型で証明する。モニック性はこの同型には不要。
`Andre/MonicFrobeniusCoefficient.lean` は、raw φ/p 包の最初の係数剰余イデアルを
`(p, f_s(Y_s)^p | s ∈ σ)` と同定し、その実商を A/p 上の通常モニック族商に同定する。
E1.7 を適用し、任意濃度の正次数モニック族について忠実平坦性を得た。
零係数環も許し、自由性や遷移射の単射性を仮定しない。

`Andre/MonicRawModPFlat.lean` は一般 δ 除算包の既存剰余計算を再利用する。
その実 raw mod p 商に A/p の係数作用を明示し、代表元公式から元の標準係数射と一致することを
確認した。この作用について剰余の忠実平坦性を証明した。
`Andre/MonicRawCompletelyFlat.lean` は G4 の既存 ghost 単射定理を内部で供給し、
通常剰余テンソルと実商の A/p 代数同型、E1.5 の raw p 正則性、主元の判定を接続する。
主要公開型は次のとおり。

```lean
theorem monicFamilyRaw_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (f : σ → Polynomial A)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    (hdp : D.IsDistinguished (p : A)) :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)})
      (DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ D)
        (p : MvPolynomial σ A)
        (fun s : σ => DeltaStructure.frobeniusLift
          (polynomialRankOneDeltaStructure σ D) (monicRelation (f s) s)))
```

`perfectPrismMonicFamilyRaw_isCompletelyFaithfullyFlat` は同じ結論で、D・hpA・hdp の代わりに
`(P₀ : OrientedPrism p A) (hP : P₀.deltaStructure.IsPerfect)` を受け取る。
δ 構造には P₀.deltaStructure を用い、hf と hdeg はそのまま要求する。
完全 δ 構造の p 正則性と、完全 prism の p 完備性から δ(p) の単元性を供給する。
外部の ghost 単射仮定・有限性仮定・他レーンの未証明仮定は残さない。

BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の補助 pd 計算に相当する。
Prop 7.11 を使う原典とは異なる、任意族の通常関係商と明示係数射を経る証明である。
補助 φ(f)/p 包の結果であり、f/d 包とその perfectoid 商の忠実平坦性を証明したわけではない。
実導来 pd 比較、無限 p 冪根変数の自由基底、最終候補の p 完全忠実平坦性は未完成。
`exists_monicRootedPerfectoidExtension` は引き続き未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4129 jobs）。
専用監査は新規 31 公開宣言を追加し、`assert_no_sorry` と生成宣言を含む 345 宣言の
標準 3 公理限定検査に成功した（終了コード 0）。

### E1.9：補助 raw 包の実導来 mod p 入力と δ 完全化

新規 `Andre/MonicRawDerivedReduction.lean` は、raw 包の元の係数射 j による
`baseChangeScalarModule j` を固定し、標準 augmentation による実導来 p 還元の離散化を証明する。
`monicRaw_modP_homology_isZero` は全 i ≠ 0 の実ホモロジー消滅を、
`monicRaw_modPH0_faithfullyFlat` は同じ実還元の H⁰ の A/p 上忠実平坦性を与える。
前提は E1.8 の D、f、hpA、hf、hdp（H⁰ の忠実性には加えて hdeg）。
制限加群と標準 raw 作用の比較は恒等関数による A 線形同型で明示し、
単なる環同型から剰余の元の係数作用を推論していない。

新規 `Andre/MonicRawPerfectionFlat.lean` は、一般 δ 完全化の既存剰余比較を再利用する。
一般定理の第二基底元を零として A/(p,0) を A/p に同定し、上記実導来入力を適用した。
Frobenius 各段の図式と余極限の証明を複製していない。
主要公開定理の型は以下。局所的に定めた代数作用も明記する。

```lean
theorem monicRawPerfection_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (f : σ → Polynomial A)
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    let E := polynomialRankOneDeltaStructure σ D
    let F := deltaAdjoinDivisionStructure E (p : MvPolynomial σ A)
      (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
    letI := monicRawPerfectionAlgebra D f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)}) (DeltaPerfection F)
```

係数射 `monicRawPerfectionCoefficientMap D f` は実 raw 係数射と完全化の第零段射の合成。
任意族・零係数環を許し、外部 ghost 単射仮定は残さない。
`monicRawPerfection_residueTensor_faithfullyFlat` は同じ A 作用の通常剰余テンソルの
忠実平坦性を、`monicRawPerfection_p_smul_regular` は p スカラーの正則性を与える。
後者自体には hf、hdeg、hD、hdp を要求しない。

BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の補助計算であり、原典の Prop 7.11 を使う
証明とは異なる経路。ここでの完全化は Frobenius 余極限のみで、p 進完備化前である。
f/d 包の実導来 pd 比較、無限 p 冪根変数の自由基底、最終 perfectoid 候補の
p 完全忠実平坦性は引き続き未完成。目標存在定理は未宣言であり、本工程を完成と数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4180 jobs）。
専用監査も終了コード 0。新規 14 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 442 宣言の推移的な公理依存が標準 3 公理のみであることを確認した。

### E1.10：補助 raw 包の p 進完備 δ 完全化への保存

新規 `Andre/MonicRawPCompletionFlat.lean` は、E1.9 の Frobenius 余極限を既存の
`PCompletedDeltaPerfection` で p 進完備化する。開イデアル商の既存比較を再利用し、
元の A の係数像を保つ剰余環同型と A/p 線形同型を明示した。
通常剰余テンソルの忠実平坦性を移し、完全 δ 構造の p 正則性と主元判定を組み合わせる。

主要公開型：

```lean
theorem monicRawPCompletedPerfection_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (f : σ → Polynomial A)
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    let E := polynomialRankOneDeltaStructure σ D
    let F := deltaAdjoinDivisionStructure E (p : MvPolynomial σ A)
      (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
    letI := monicRawPCompletedPerfectionAlgebra D f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)}) (PCompletedDeltaPerfection F)
```

この代数構造の係数射は `pCompletedDeltaPerfectionMap F` と実 raw 係数射の合成。
`monicRawPCompletedPerfectionResidueEquiv_mk` と同じ A/p 線形比較により、
環同型だけから元の係数作用の忠実平坦性を推論していない。
族は任意濃度で、外部 ghost 単射仮定を要求しない。
線形性の具体的作用の照合では、既存冪根版と同じ局所 heartbeat 上限 800000 が必要だった。

BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の補助計算。
Prop 7.11 を使う原典と異なる経路であることを docstring に記載した。
これは補助 φ(f)/p 包の完備化であり、一般 f/d 包との実導来比較および最終 perfectoid 商の
p 完全忠実平坦性は未完成。無限 p 冪根変数の自由基底も未証明。
目標存在定理は未宣言であり、補助完備化の定理を担当全体の完成と数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4182 jobs）。
専用監査も終了コード 0。新規 11 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 525 宣言について標準 3 公理のみの推移的公理依存を確認した。

### E1.11：一般 f/d 包の raw (p,d) 剰余の忠実平坦性

新規 `Andre/MonicPrismaticCoefficient.lean` は、一般 f/d 包の初期係数イデアル
`deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (fun s => monicRelation (f s) s)`
を `(p,d)` の係数拡張と全族関係イデアルの和に同定する。
実商を `PolynomialFamilyQuotient (fun s => (f s).map (Ideal.Quotient.mk (Ideal.span {p,d})))`
に写す具体的環同型、元の係数像を保つ公式、標準 A/(p,d) 代数同型を構成した。
`monicPrismaticCoefficient_faithfullyFlat` は hf・hdeg からその初期係数商の忠実平坦性を証明する。
δ 構造、p 正則性、d 正則性、族の有限性はこの係数商には不要である。

新規 `Andre/MonicPrismaticRawResidue.lean` は、一般 δ 除算包の既存の実剰余表示に接続する。
初期係数商の標準射と raw 剰余の標準射を合成し、元の A の各係数の標準像を保つことを証明した。
G4 から ghost 単射を内部で供給する最終公開型は以下。

```lean
theorem monicPrismaticRawResidue_faithfullyFlat_of_distinguished
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished d) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicPrismaticRawResidueAlgebraOfDistinguished D d f hpA hdp
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      (DeltaAdjoinDivisionResidue (polynomialRankOneDeltaStructure σ D)
        (MvPolynomial.C d) (fun s : σ => monicRelation (f s) s))
```

これにより補助 φ(f)/p 包に限らず、最終構成の一般 f/d 包の raw 実剰余まで進んだ。
全族の初期係数商から raw 剰余への一般忠実平坦性と、初期係数商の通常モニック忠実平坦性を
元の係数射で合成している。外部 ghost 仮定・有限性・未証明の他レーン仮定は残さない。

BS Rem 7.15（著者版 p.62）の一般除算包の剰余計算に対応する。
Prop 7.11 を使う原典と異なる明示係数商による経路であることを記録した。
raw 剰余の通常忠実平坦性であり、raw single の実導来 (p,d) 還元との同定、
完備化後の離散性・最終 perfectoid 商の p 完全忠実平坦性は未完成。
無限 p 冪根変数の自由基底と目標存在定理も引き続き未証明・未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4184 jobs）。
専用監査も終了コード 0。新規 16 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 594 宣言の公理依存が標準 3 公理のみであることを確認した。
