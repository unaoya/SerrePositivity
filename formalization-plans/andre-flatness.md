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

### 残る範囲

1. 有向余極限の p 進完備化の perfectoid 性（特に p ねじれを許す Fontaine 核の単項性）。
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
