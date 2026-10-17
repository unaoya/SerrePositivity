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

### E3.9：perfectoid 有向系の完備化と非可算極限

`PresentationColimit.lean` と `PerfectoidCompletionColimit.lean` を追加。

- `isIntegralPerfectoid_adicCompletion_ringDirectLimit`：最小元を持つ有向添字 Type u 上の
  perfectoid 環の有向系について、環余極限の通常 p 進完備化は perfectoid。
  遷移射の単射性・完全平坦性・p 正則性を仮定せず、零環も含む。
- `isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound`：上記の系が p 完全忠実平坦で、
  すべての可算添字部分集合が上界を持つなら、未完備余極限自体が perfectoid。
- `ainfMap` とその恒等・合成・δ 構造の保存、`ainfSystem` を公開。
- `presentationLimitMap` と標準段射上の公式、全射性・共通単項核の保存、および
  `isIntegralPerfectoid_adicCompletion_of_presentationDiagram` を公開。

**原典・経路の記録：** BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、
Thm 7.14（p.61）の極限操作を既存 Fontaine 表示と実 PD 完備化の普遍性で補足。
各段の Fontaine 全射の自然性と、最小段の distinguished 生成元の像による核表示は既証定理を再利用。
余極限の核の元を一段で代表し、零となる等式を後の段に移して共通生成元で割る。
最終的な完備化が非零の場合には、各段からの標準環射により各段の非零性を取り出すので、
零段を除外する追加仮定はない。非可算極限では E3.2 の完備性と標準完備化同型を使う。

対象 build 終了コード 0（3503 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 52 宣言の assert_no_sorry と全 127 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
**未完了：** 完備化による p 完全忠実平坦性の保存と超限塔の構成。
この工程は作業 1 を証明したもので、条件付き Thm 7.14 の完成とは数えない。

### E3.10：有界ねじれ環の通常完備化の完全忠実平坦性

`BoundedCompletion.lean` を追加。

- `isCompletelyFaithfullyFlat_adicCompletion_of_bounded_torsion`：任意の可換環 R と a:R について、
  `(∃ N, ∀ n x, a^n*x=0 → a^N*x=0)` の下で、通常の a 進完備化が標準 R 作用に関して
  `(span {a})` 完全忠実平坦となる。a 正則性・Noether 性・元環の完備性は不要。
- `boundedPrincipalCompletionAdicAlgEquiv`：実主イデアル導来完備化の H0 と通常完備化の
  R 代数同型を、元の二つの普遍性を照合して構成。
- 導来完備化単位の主イデアル商への実導来底変換が、a 正則性なしで同型となること、
  実完備化の次数 0 集中・有界ねじれ・古典的完備性・剰余 Tor 消滅を順に公開。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の極限操作に必要な補足証明。
冪ねじれ対象とのテンソルが実完備化単位を同型にする既証定理を、実導来底変換の自然性で移す。
剰余の離散性と平坦性から、既存の有界ねじれ環上の純性定理を適用。
H0 の有界ねじれと実導来完備性から古典的完備性を得る。
剰余への実導来底変換の離散性を Tor 消滅に移し、通常剰余の忠実平坦性と合わせる。
この工程で有界ねじれを通常／導来完備化の比較の代用にせず、比較同型そのものを証明した。

対象 build 終了コード 0（3624 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 63 宣言の assert_no_sorry と全 154 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
**未完了：** 各段から余極限・完備化への射の完全忠実平坦性との合成、超限塔の構成。
条件付き Thm 7.14 はまだ未証明。

### E3.11：標準極限射の完全忠実平坦性と終段の三性質

`CompletedMaps.lean` と `Terminal.lean` を追加。

- `isCompletelyFaithfullyFlat_adicCompletion_comp`：終域に有界 p 冪ねじれがあれば、
  p 完全忠実平坦な射と標準完備化射の合成は p 完全忠実平坦。
- `isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot`：最小段から各段への射が
  p 完全忠実平坦なら、環余極限への最小段射も p 完全忠実平坦。
- `isCompletelyFaithfullyFlat_completedRingDirectLimit_of_orderBot`：各段が perfectoid なら、
  上記射と p 進完備化射の標準合成も p 完全忠実平坦。E3.7 の境界 1 を E3.10 に適用。
- `omegaOne_directLimit_properties`：実際の ω₁ 塔について、全段 perfectoid・全遷移射 p 完全忠実平坦・
  各後続段で全正次数モニックの根がある、という引数から、余極限の perfectoid 性・
  初段からの p 完全忠実平坦性・絶対整閉性を同時に結論する。
- `omegaOneIndex_orderBot` は既存の非空整列順序の最小元構造を供給する。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の極限操作を、E3.1–E3.10 の結果で合成。
環余極限と代数の非交和余極限の比較は、束の型の違いによる非公開実装の簡約に依存せず、
実際の二つの環普遍写像を作って逆写像を検証した。元の最小段の係数作用で線形性も確認。
ω₁ 添字は既存 E3.3 の `Ordinal.ToType (Ordinal.omega 1)` の小さい表現を共用する。

対象 build 終了コード 0（3626 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 68 宣言の assert_no_sorry と全 162 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
**未完了：** 訂正済み step だけを入力とする超限塔の構成。塔のデータを仮定した上記の
終段定理を、条件付き Thm 7.14 の完成として数えない。

### E3.12：遷移射の単射性を要求しない非可算極限

`CountableRelations.lean` を追加。

- `exists_stage_countable_equalities`：一段の元の可算族に関する等式が余極限で成り立てば、
  可算添字集合の上界条件の下で、それらすべてが後の一段で成り立つ。
- `isAdicComplete_directLimit_of_countable_upperBound_without_injective`：各段が p 進完備なら、
  同じ上界条件の下で余極限も p 進完備。遷移射の単射性・平坦性は不要。
- `isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound_without_flatness`：
  最小元を持つ有向添字上の perfectoid 環の系について、上界条件だけから余極限自体の
  perfectoid 性を得る。p 完全平坦性・単射性・p 正則性を仮定しない。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の非可算極限段の補足証明。
E3.2 では一段への単射性により等式を反映していた。ここでは各等式が成り立つ段も可算個選び、
それらの共通上界に移すため、単射性を取り除ける。
Cauchy 列だけでなく、全差の冪割算の証人とそれらの等式も一段へ降ろして完備性を適用する。
この強化により、固定初段上の perfectoid・p 完全忠実平坦代数の通常の代数射の圏で
超限反復を構成する経路を採れる。遷移射の完全忠実平坦性を最終結論の代用にはしない。

対象 build 終了コード 0（3627 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 71 宣言の assert_no_sorry と全 166 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
**未完了：** 固定初段上の極限の代数構造と普遍性、訂正済み step による超限塔の構成。
条件付き Thm 7.14 はまだ未証明。

### E3.13：固定基底の環余極限と完備化の普遍写像

`AlgebraColimit.lean` と `CompletionUniversal.lean` を追加。

- `algebraRingDirectLimitEquiv` と標準段射上の公式：環余極限と非交和代数余極限を
  明示的な二つの普遍環射で比較。束の型による環演算の定義的同一性を仮定しない。
- `algebraRingDirectLimitBaseMap`・`algebraRingDirectLimitAlgebra`・`algebraRingDirectLimitOf`：
  共通の任意基底からの係数写像と代数構造、各段の代数射を実現。
- `isCompletelyFaithfullyFlat_algebraRingDirectLimit`：任意のイデアル I に関する
  各段の完全忠実平坦性を、元の共通基底作用の環余極限へ移す。
- `algebraRingDirectLimitLift` と標準段射上の公式：両立する代数射の普遍写像を供給。
- `natAdicCompletionLift`・`natAdicCompletionLift_of`・`natAdicCompletion_ringHom_ext`：
  任意の自然数 p について、p 進完備な環への環射の通常完備化からの延長、
  元の係数像との両立性と一意性を証明。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の超限反復に必要な代数構造と普遍性の補足。
既存の実際の余極限・通常完備化を用いる。係数作用を元の標準環射から定めて両立性を検証。

対象 build 終了コード 0（3629 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 83 宣言の assert_no_sorry と全 203 宣言の再帰監査に成功。
標準 3 公理のみ。全公開宣言の完全型を #print で確認。
**未完了：** perfectoid・p 完全忠実平坦な代数の圏における実余極限の普遍性、
訂正済み step による後続操作と超限反復。条件付き Thm 7.14 はまだ未証明。

### E3.14：固定初段上の塔の代数の圏と実余極限

`AlgebraCategory.lean` を追加。

- `AndreTowerAlgebra R p`：台環 Type u・標準係数環射 R→B・perfectoid 性・その射の
  toAlgebra に関する p 完全忠実平坦性を保持する。圏の対象の型のみ Type (u+1) に置く。
- `AndreTowerAlgebra.Hom` と圏構造：射は係数射と両立する通常の環射。
  射そのものの完全忠実平坦性を構造の仮定に追加しない。
- `AndreTowerAlgebra.colimitObject`・`colimitOf`・`colimitCocone`：元の環余極限の
  p 進完備化を、標準係数作用と標準段射を持つ実対象・余錐として構成。
- `AndreTowerAlgebra.colimitDesc`・`colimitDesc_fac`・`colimitIsColimit`：
  任意の余錐への元の普遍写像、その因子分解、一意性を証明。
- `andreTowerAlgebra_hasColimitsOfShape`：任意の非空整列線形順序 Type u による余極限を供給。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の超限反復を、固定初段からの
完全忠実平坦性を対象の性質とする圏の反復として実装する。環余極限と通常完備化の
実普遍性を逐一検証し、極限対象の存在を公理や仮定にはしない。
各段から初段への係数射の完全忠実平坦性は E3.5・E3.10・E3.13 で保持される。
終段の自動的完備性には E3.12 を使えるため、圏の全射に単射性を要求する必要がない。

対象 build 終了コード 0（3664 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 111 宣言の assert_no_sorry と全 329 宣言の再帰監査に成功。
標準 3 公理のみ。構造・射・係数作用の公開型を #print で確認。
**未完了：** 訂正済み step から後続操作を作り、実際の ω₁ 反復を構成する工程。
条件付き Thm 7.14 はまだ未公開。

### E3.15：訂正済み step に相対的な Thm 7.14 の超限反復

`Existence.lean` を追加。公開主定理は
`SerrePositivity.BhattScholze.Andre.Transfinite.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`。
入力の `step` は、ユーザー承認済みの正次数条件だけを追加した次の型をそのまま使う。

```lean
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)
    (step : ∀ (B : Type u) [CommRing B] (_hB : IsIntegralPerfectoid B p)
      {σ : Type u} (f : σ → Polynomial B),
      (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
      ∃ (T : Type u) (_ : CommRing T) (φ : B →+* T) (ρ : σ → T),
        IsIntegralPerfectoid T p ∧
        (letI := φ.toAlgebra;
          IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) T) ∧
        ∀ s, (f s).eval₂ φ (ρ s) = 0) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S
```

結論の存在量化・代数構造・三性質は Inputs の元の主張と同じ。追加前提は上記 step のみ。
`exists_root_successor` は全正次数モニック多項式の部分型を一度に step に入力する。
`rootSuccessor`・`rootSuccessorMap`・`rootSuccessorMap_roots` と `rootSuccessorStructure` が
同じ選択に付随する後続対象・射・根の存在と、初段 R の後続操作を構成する。
`isCompletelyFaithfullyFlat_self` は初段の恒等係数射の条件を検証する。
`andreTowerAlgebra_hasIterationOfShape` は全体と真の極限初期区間に E3.14 の実余極限を供給する。

**原典・証明経路の記録：** BS Thm 7.14（著者版 p.61）の全モニックへの根添加の超限反復を、
Mathlib の `SmallObject.SuccStruct.iterationFunctor` で実装。
原典の環拡大の塔に対し、実装では固定初段 R からの完全忠実平坦性を各対象に保持する圏を使う。
後続射は step の完全忠実平坦射。極限の全遷移射の完全忠実平坦性を追加仮定とせず、
各段の R 上の完全忠実平坦性を E3.5・E3.10 によって保つ。
ω₁ 未満の真の極限段では通常 p 進完備化した環余極限を実余極限として用いる。
終段 S は完備化前の環余極限であり、可算個の元・割算の証人・等式の同時降下から
自動的 p 進完備性を得る（E3.12）。そのため、終段で完備化後の新係数を扱う問題は生じない。
各多項式の有限係数は一段に入り、その後続段の根を終段に写す。
後続同型との両立性は元の反復函手の射の公式と `Polynomial.hom_eval₂` で照合する。
各環・終段・添字は Type u。圏の対象型のみ Type (u+1)。

対象 build 終了コード 0（3665 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 119 宣言の assert_no_sorry と全 339 宣言の再帰監査に成功。
標準 3 公理（propext・Classical.choice・Quot.sound）のみ。
`#print` で主定理に余分な塔・余極限・ねじれ・比較の仮定が残らないことも確認した。

**未解消：** 指定 step 自身の A1 による構成はこの工程の成果に含まれない。
これは step に相対的な証明であり、無条件の BS Thm 7.14 の完成・引用解消としては数えない。
Inputs の既存 sorry は編集していない。

### E3.16：A1 の一元拡大を任意の perfectoid 基底へ移送

`SingleRoot.lean` を追加。

- `exists_monicRootPerfectoidExtension`：任意の perfectoid 環 R 上の一つの正次数モニック多項式に、
  同じ Type u の p 完全忠実平坦な perfectoid 拡大で根が存在する。追加仮定なし。
- `isCompletelyFaithfullyFlat_ringEquiv`：環同型の toAlgebra の作用について、
  任意のイデアルに関する完全忠実平坦性を R 自身から線形同型で移す。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）。
A1 の `PerfectPrismMonicRootedExtension.lean` の一元存在定理を利用する。
非零基底は既存 `exists_perfectoidTrialPrism` で実 Fontaine・PD 構成の完全 prism 商と環同型にし、
その商へ多項式を移す。環同型の単射性で次数が保存され、モニック性も保存される。
A1 の商上の拡大射と基底環同型の逆射を合成し、元の toAlgebra の作用に関する
完全忠実平坦性を E3.6 で合成する。零環には恒等射を使う。
A1 の一元拡大の対象 build を実行し、終了コード 0（4242 jobs）を確認した。
他レーンのファイル・記録・ハンクは編集しない。

集約対象 build 終了コード 0（4344 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 121 宣言の assert_no_sorry と全 341 宣言の再帰監査に成功。
A1 の一元拡大への推移的依存も標準 3 公理のみ。
**未完了：** 一元の根添加を任意の添字族に広げ、E3.15 の指定 step を解消する工程。

### E3.17：任意族 step の解消と、元の署名の無条件 Thm 7.14

`FamilySaturation.lean`・`FamilyExtension.lean`・`Theorem714.lean` を追加。

- `exists_allBasePolynomialRoots`：固定基底 R の族 f:σ→Polynomial R に対し、各対象で各一項の
  根を持つ拡大が可能なら、全族の根を持つ一つの塔の代数が存在する。
- `exists_familyRoot_successor`：E3.16 の一元存在定理を現在の対象に適用し、
  元の R 係数の族の任意の一項の根を後続対象に得る。非零枝でモニック性から次数が保存され、
  零環枝では恒等射で既に根を持つ。
- `exists_monicFamilyRootedPerfectoidExtension`：指定された正次数条件付き step そのものを、
  有限性・追加のねじれ・比較・存在仮定なしで証明。入力は R の perfectoid 性と
  `(∀ s, (f s).Monic ∧ 0 < (f s).natDegree)` のみ。全ての環と σ は Type u。

無条件の公開主定理（namespace は `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S
```

**原典・証明経路の記録：** BS Thm 7.14（著者版 p.61）の第一文の元の署名を証明した。
一段拡大の根の部分には、A1 の完全 prism 商上の一元拡大と E3.16 の基底移送を使う。
任意族の step を得るため、原典の一括根添加に対し、ここでは固定係数族の一元飽和を補足する。
`c = Order.succ (Cardinal.mk σ ⊔ Cardinal.aleph0)` の始順序数の小さい表現に沿って反復。
各後続段では、全族が解決済みなら恒等射を使い、そうでなければ未解決の一項を解決する。
終段で未解決なら、各段で新たに解決した添字は異なり、濃度 c の添字型から σ への単射ができ、
`c ≤ Cardinal.mk σ ≤ Cardinal.mk σ ⊔ Cardinal.aleph0` となって後続基数の性質に矛盾する。
根の存在は全ての係数両立環射で保存され、極限の通常完備化を経ても元の R 係数の根は保たれる。
この補助反復では係数を固定しているため、完備化後の新係数を降下させる議論は行わない。
得られた任意族 step を E3.15 の ω₁ 反復に入力して、新係数も含む全正次数モニックに根を得る。
従って主定理は ω 回反復後の完備化から絶対整閉性を推論していない。

集約対象 build 終了コード 0（4347 jobs、新規モジュール警告なし）。
専用監査終了コード 0、公開全 131 宣言の assert_no_sorry と全 352 宣言の再帰監査に成功。
推移的公理依存は標準 3 公理のみ。主定理の #print と元の存在型への明示的な適用例により、
step・塔・単射性・平坦性・有界ねじれなどの追加仮定が残らないことを確認した。

**保存時点の残り：** 無条件主定理を公開報告し、その後の別コミットで Inputs の既存 sorry を置換する。
A1 のファイル・ハンクは本レーンのコミットに含めない。

### E3.18：一般有向系の保存と、報告後の Inputs 置換

`DirectedCompletion.lean` を追加。完了確認で、E3.9 の最小元仮定を外した一般形も証明した。

- `isIntegralPerfectoid_adicCompletion_of_directed_perfectoid`：任意の非空有向前順序 Type u 上の
  perfectoid 環の有向系について、環余極限の通常 p 進完備化は perfectoid。
  最小元・遷移射の単射性・p 完全平坦性・p 正則性は仮定しない。
- `isCompletelyFaithfullyFlat_completedAlgebraRingDirectLimit`：固定基底上の p 完全忠実平坦な
  perfectoid 代数の任意の非空有向系について、通常 p 進完備化への標準係数射も
  p 完全忠実平坦。係数射は元の共通係数射と標準完備化射の合成そのもの。

**原典・経路の記録：** BS Thm 7.14（著者版 p.61）の一般の有向極限の補足。
Fontaine 核生成元は任意の一段で選ぶ。核の元が零となる段と基点段の共通上界へ移し、
その段の核表示を使うことで、全体の単項核を同定する。最小元を仮定する必要はない。
完全忠実平坦性には共通基底の余極限保存と、被約な未完備余極限の p 冪ねじれ境界 1 を用いる。

無条件主定理は `b2a17a37` に保存し、公開定理名・正確な存在結論・前提と監査結果を
ユーザーに報告した**後**、`Inputs/AndreFlatness.lean` の既存 sorry を既証定理の適用に置換した。
公開定理の宣言から `:= by` 直前までが置換前と完全に同じ文字列であることを検査済み。
Inputs の docstring も、文献からの未証明入力という旧記述から証明済み入口へ更新した。
A1 のファイル・ハンクは編集・同梱していない。

`set -o pipefail; lake build` の対象は Inputs、E3 集約、および直接の既存利用先
`AndreCompatibleRootsConditional`・`AndreSurjectivityConditional`。
終了コード 0（4381 jobs、新規・変更対象モジュールの警告なし）。
専用監査終了コード 0、公開全 134 宣言の assert_no_sorry と全 370 宣言の再帰監査に成功。
Inputs の公開定理も監査対象に含め、推移的公理依存は標準 3 公理のみ。
E3 の全ソースと Inputs に sorry・axiom 宣言がないこと、ルートへの E3 集約 import が 1 行のみであることも確認。

この保存単位は無条件版の主定理の報告・保存と分け、Inputs 置換の別コミットにする。

### 残る範囲

今回依頼された Thm 7.14 の第一文・元の存在型について、未解消の前提や既存 sorry は残らない。
指定 step は E3.17 で証明し、Inputs の元の公開署名は E3.18 で既証定理へ接続した。
BS Thm 1.17(1) は変更せず、Cor 8.12 の宣言・使用・形の仮定は追加していない。
原典の mod p ind-syntomic という強化は今回の結論に含めず、証明したものとも数えない。

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

### E1.12：有限モニック族の全有限 δ 深さの実残余 Koszul 分解と導来評価

新規 `Andre/MonicRelationRegularSequence.lean` は、異なる有限添字のモニック関係が
任意係数環上の弱正則列をなすことを証明する。先行添字集合の商の後続正則性を各位置に適用する。
`monicRelation_fin_isWeaklyRegular` の型は
`(f : σ → Polynomial A) → (∀ s, (f s).Monic) →
 (s : Fin n → σ) → Function.Injective s →
 RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
   (List.ofFn fun i => monicRelation (f (s i)) (s i))`。
正次数や係数環の非零性は不要。負の関係族にも同じ結果を公開した。

新規 `Andre/MonicPrismaticFirstResidueKoszul.lean` は、二重多項式係数商の表示により、
最初の δ 関係を負のモニック関係へ移して実 (p,d) 商上の弱正則性と Koszul 分解を証明する。
この最初の段には係数環の p 正則性も δ(d) 単元性も不要。
新規 `Andre/MonicPrismaticFiniteResidueKoszul.lean` は、一般 δ 除算の既存有限深さ定理へ
初項入力を渡し、全有限 δ 深さの弱正則性、評価関係の Koszul 分解、実残余自由 δ 射に沿う
有限源グラフ商の全高次 Tor 消滅を証明する。これには hpA と δ(d) の単元性を用いる。

新規 `Andre/MonicPrismaticSourceResidue.lean` は、有限添字族の有限深さの Tor 消滅を
既存の逐次余極限定理と Tor 対称性で全評価源へ移す。標準 augmentation による主要公開型：

```lean
def monicPrismaticResidueSourceDerivedIso
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
    {m : ℕ} (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    let P := MvPolynomial σ A
    let L := RelativeFreeDeltaRing (R := P) σ
    let E := polynomialRankOneDeltaStructure σ D
    let r := fun t : σ => monicRelation (f t) t
    let K := Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
    let ψ := (Ideal.Quotient.mk K).comp (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
    let β := deltaDivisionSourceEval E r
    (boundedAboveDerivedBaseChange β).obj
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule ψ)) ≅
    boundedAboveDerivedSingleFunctor.obj
      (ModuleCat.of P (DeltaAdjoinDivisionResidue E (MvPolynomial.C d) r))
```

全評価源の結果に外部 ghost 仮定や余極限保存仮定は残さない。有限性は明示した s のみで、
正次数は不要である。source の射・商射・評価射を固定して、標準 augmentation と通常残余テンソル
の具体的同型を合成した。抽象的な同型の存在から係数作用を推論していない。

BS Rem 7.15（著者版 p.62）の実導来剰余比較の評価側であり、Prop 7.11 を使う原典とは
異なる経路である。残るのは元の A/(p,d) 係数側への比較、完備化後の離散性、
最終 perfectoid 商の p 完全忠実平坦性、無限 p 冪根変数の自由基底、任意族への最終接続。
目標存在定理は引き続き未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4188 jobs）。
専用監査も終了コード 0。新規 15 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 703 宣言の推移的公理依存が標準 3 公理のみであることを確認した。

### E1.13：実自由 δ 源商から元の A/(p,d) 上への導来比較

新規 `Andre/MonicPrismaticCoefficientReduction.lean` は、実三因子還元を定義し、
一般結合子と E1.12 の標準導来評価比較を合成して raw 剰余の single に同定する。
新規 `Andre/MonicPrismaticQuotientDerived.lean` は実源商への基底変更対象
`MonicPrismaticSourceQuotientDerived D d f` と、raw 剰余の実源商作用を明示する。
商射の全射性で H⁰ 同型の線形性を実源商へ降下し、全非零次数ホモロジー消滅と
正規化された single 比較 `monicPrismaticSourceQuotientDerivedSingleIso` を証明した。
この比較は hf、有限全列挙 s、hpA、δ(d) の単元性だけを使い、hdeg は不要。

新規 `Andre/MonicPrismaticQuotientFlat.lean` は、実源商上の H⁰ 比較を元の係数商へ制限し、
係数の代表元公式により E1.11 の raw 剰余の作用と一致させる。
新規 `Andre/MonicPrismaticPDReduction.lean` は、元の A 上の実二因子源
`MonicPrismaticSourceCoefficientObject D d f` を定義し、二重多項式係数包含に対する
既存の一般正方形比較 `deltaRootSourcePDDerivedSquareIso` を直接再利用した。
この既存比較の型はモニック関係や根関係に依存しない任意の実源対象・射影モデルを受け取る。
他レーンのファイルは変更していない。

主要公開型（Y の略記を明示）：

```lean
theorem monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
    {m : ℕ} (s : Fin m ≃ σ)
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    let I := Ideal.span {(p : A), d}
    let Y := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
      (MonicPrismaticSourceCoefficientObject D d f)
    Module.FaithfullyFlat (A ⧸ I)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) 0).obj Y.obj)
```

`monicPrismaticSourceCoefficientPDResidue_homology_isZero` は同じ Y について
`(i : ℤ) → i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) i).obj Y.obj)`。
同じ前提から hdeg だけを除く。
`monicPrismaticSourceCoefficientPDResidueIso` は同じ Y を、実源商を経由する元の A/(p,d) 作用を
持つ raw 剰余の single に具体的に同定する。外部 ghost・余極限保存仮定は残さない。

BS Rem 7.15（著者版 p.62）の実導来剰余比較を元の係数環上まで進めた。
Prop 7.11 を使う原典と異なる明示関係・実作用の比較による証明である。
残るのは逐次 p,d 実完備化後の離散性と一般 f/d 候補との環・δ 比較、
最終 perfectoid 商の p 完全忠実平坦性、無限 p 冪根変数の自由基底、任意族の最終接続。
目標存在定理は引き続き未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4192 jobs）。
専用監査も終了コード 0。新規 22 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 964 宣言の推移的公理依存が標準 3 公理のみであることを確認した。

### E1.14：逐次実完備化と生成元冪商、完全 prism 上の源の離散性

新規 `Andre/MonicPrismaticIteratedResidue.lean` は、一般 f/d 源に実 p 完備化、実 d 完備化を
この順に施した `MonicPrismaticSourceIteratedPDCompletion D d f` を定義する。
p と d が係数環で個別に正則なら実 (p,d) 還元が元の実還元と同型であることを、一般の
完備化単位の既存比較から証明した。比較は二つの標準単位の合成に関する公式を満たす。
有限族について実剰余の全非零次数ホモロジー消滅と H⁰ の忠実平坦性を E1.13 から移した。
d mod p の正則性を要求していない。

新規 `Andre/MonicPrismaticSourceComplete.lean` は、同じ実対象の p,d 両方向の導来完備性と、
正則な d の任意冪商への実還元の商環上での p 導来完備性を証明する。
これらの完備性自体には hf・hdeg・有限性は不要。
新規 `Andre/MonicPrismaticCanonicalPowerResidue.lean` は、A/(p,dⁿ) の標準冪零商による
実還元を raw 剰余の single に、元の作用を保って同定した。
新規 `Andre/MonicPrismaticSourcePowerInputs.lean` は、この入力に既存の冪零厚化の判定 G10 を
適用し、正の n について A/(p,dⁿ) 還元の純性と H⁰ の平坦性を得た。
さらに A/(dⁿ) 還元の p 導来完備性と、その標準 mod p 還元の純性・平坦性を、
同じ実対象の G9 入力 `monicPrismaticSourceGeneratorPower_G9_inputs` に束ねた。

新規 `Andre/PerfectPrismMonicSourceDiscrete.lean` は、完全 prism の既存定理から
p 正則性、生成元 d の正則性、δ(d) の単元性、A/(dⁿ) の p 冪ねじれ上界 pⁿ を内部で供給する。
G9 で正の生成元冪商の離散性を得て、生成元商の離散性と d 導来完備性で元の源の純性を導いた。
主要公開型は次のとおり。

```lean
theorem perfectPrismMonicSource_pure
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ t, (f t).Monic)
    (hdeg : ∀ t, 0 < (f t).natDegree) {m : ℕ} (s : Fin m ≃ σ) :
    let X := MonicPrismaticSourceIteratedPDCompletion P.deltaStructure P.generator f
    X.obj.IsGE 0 ∧ X.obj.IsLE 0
```

`perfectPrismMonicSource_homology_isZero` は同じ X の全 i ≠ 0 に対する実ホモロジー消滅。
`perfectPrismMonicSourceSingleIso` は
`X.obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
 ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj)`。
外部 ghost 仮定・有界ねじれ仮定・単元選択の仮定は残さない。
有限性、モニック性、正次数を公開の前提に明示する。

BS Rem 7.15（著者版 p.62）の実 prismatic 源の離散性に対応する。
Prop 7.11 を使う原典とは異なる、具体的な係数商・G10・G9 を経る証明である。
これで「逐次実完備化源の離散性」は有限正次数モニック族で証明済みになった。
残るのは同じ実 H⁰ と raw PD 完備化環および最終 f/d 候補との環・δ 比較、
最終 perfectoid 商の p 完全忠実平坦性、無限 p 冪根変数の自由基底、任意族への最終接続。
目標存在定理は引き続き未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4228 jobs）。
専用監査も終了コード 0。新規 25 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 1177 宣言の推移的公理依存が標準 3 公理のみであることを確認した。

### E1.15：同じ実 H⁰ から raw PD 環への比較と完全忠実平坦性

新規 `Andre/MonicPrismaticRawSourceComparison.lean` は、評価射と除算源射の通常テンソルを
raw f/d 包に同定し、元の二因子実導来源から raw single への標準 augmentation を構成する。
H⁰ に同型を誘導することと、逐次完備化比較が二つの元の標準単位に両立することを証明する。
`Andre/MonicPrismaticRawCoefficients.lean` は、元の二重係数制限の作用と raw 包の標準 A 作用を
恒等関数の A 線形同型で照合する。
`Andre/MonicPrismaticSourceNonpositive.lean` と `MonicPrismaticSourceCompletionH0.lean` は、
元の実源と raw single の非正性を明示的射影モデルで証明し、標準 augmentation が
同じ逐次完備化後にも H⁰ 同型を誘導することを、既存の一般 H⁰ 完備化比較から得る。

新規 `Andre/MonicPrismaticRawCompletionRestriction.lean` は G8 を同じ実係数射に二度適用し、
A 上で完備化した raw 対象を raw 環上の実逐次完備化の係数制限へ同定する。
この比較にも両標準完備化単位を保つ公式を付けた。
`Andre/MonicPrismaticRawPDComparison.lean` は既存の一般二座標反射比較
`iteratedPDH0LinearEquiv` を直接再利用し、次の A 線形同型を構成する。

```lean
def monicPrismaticSourcePDH0Iso
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) :
    let E := polynomialRankOneDeltaStructure σ D
    let Raw := DeltaAdjoinDivision E (MvPolynomial.C d)
      (fun t : σ => monicRelation (f t) t)
    let c := algebraMap A Raw
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
    (ModuleCat.restrictScalars c).obj
      (ModuleCat.of Raw (PDCompletionH0 Raw p (c d)))
```

これらの比較自体にはモニック性・正次数・有限性は不要。
環同型の存在だけから元の係数作用を推論せず、raw の各標準係数像を保つ一般反射比較を使う。
`monicPrismaticRawInternalPDLinearEquiv_unit` は、Raw 上の比較がすべての raw 元の標準像を保つ。

新規 `Andre/PerfectPrismMonicRawPDCompletelyFlat.lean` は E1.14 の源の純性と上記 H⁰ 同型を
合成して、同じ A 作用の raw PD 環の single 比較を構成する。
実 (p,d) 還元の全非零次数ホモロジー消滅と H⁰ 忠実平坦性を移し、元の係数作用について
完全忠実平坦性を導く。主要公開型を、制限加群の台集合も明示して記す。

```lean
theorem perfectPrismMonicRawPD_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ t, (f t).Monic)
    (hdeg : ∀ t, 0 < (f t).natDegree) {m : ℕ} (s : Fin m ≃ σ) :
    let E := polynomialRankOneDeltaStructure σ P.deltaStructure
    let Raw := DeltaAdjoinDivision E (MvPolynomial.C P.generator)
      (fun t : σ => monicRelation (f t) t)
    let c := algebraMap A Raw
    let B := PDCompletionH0 Raw p (c P.generator)
    let M := (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw B)
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator}) (ModuleCat.carrier M)
```

有限全列挙と正次数モニック性以外の補助的な ghost・有界ねじれ・単元選択仮定は残さない。
BS Rem 7.15（著者版 p.62）の実 prismatic 源から raw PD 環への平坦性の移送。
Prop 7.11 を使う原典と異なる、実関係と標準係数作用を保つ比較による経路である。
残るのはこの raw PD 環の δ 完全化と最終 f/d 候補との環・δ 比較、
最終 perfectoid 商の p 完全忠実平坦性、無限 p 冪根変数の自由基底、任意族への最終接続。
目標存在定理は引き続き未宣言である。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4279 jobs）。
専用監査も終了コード 0。新規 38 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 1428 宣言の推移的公理依存が標準 3 公理のみであることを確認した。

### E1.16：PD 先行 δ 完全化から既存の多項式 prism 候補へ

新規 `Andre/PerfectPrismMonicPDPerfectionInputs.lean` は、raw PD 環の係数制限加群を
標準環射 `A → Raw → PDCompletionH0 Raw p (c d)` に沿う加群へ同定し、この係数射が δ 射であることを
一般 δ 完備化の既存定理で証明する。有限正次数モニック族について、その同じ標準係数射の
実 (p,d) 還元の離散性・H⁰ 忠実平坦性を E1.15 から移した。
既存の一般 δ 代数の定理へ渡し、raw PD 環を δ 完全化して再び実 PD 完備化した環の
元の (p,d) 係数作用に関する完全忠実平坦性
`perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat` を得る。

新規 `Andre/MonicPrismaticCandidateComparison.lean` は、候補台環への実 raw 射
`polynomialPrismRawMap` と元の A からの標準射 `polynomialPrismCoefficientMap` を明示する。
二つの一般比較 `deltaPDCompletionPerfectionEquiv` と `deltaPerfectionPDCompletionEquiv` を合成して、
PD 先行構成と既存の `DivisionPrismCarrier` との環同型
`monicPrismaticPDPerfectionCandidateEquiv` を構成する。
任意の raw 元の標準像および元の A 係数射を保つ公式と、A 線形加群同型を付ける。
比較自体は任意多項式族について成立し、モニック性・正次数・有限性を要求しない。

新規 `Andre/PerfectPrismMonicPrismCompletelyFlat.lean` は、係数射を保つ上記加群同型で
完全忠実平坦性を移し、標準係数射の toAlgebra の作用と恒等関数の線形同型で照合する。
主要公開型：

```lean
theorem perfectPrismMonicPrism_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ t, (f t).Monic)
    (hdeg : ∀ t, 0 < (f t).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
    let E := polynomialRankOneDeltaStructure σ P.deltaStructure
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    letI := (polynomialPrismCoefficientMap P.deltaStructure P.generator f).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator})
      (DivisionPrismCarrier E (MvPolynomial.C P.generator)
        (fun t : σ => monicRelation (f t) t))
```

有限全列挙・モニック性・正次数以外の補助的な単元・ghost・有界ねじれ仮定は残さない。
BS Rem 7.15（著者版 p.62）の原典と異なる PD 先行構成と既存候補の具体的係数比較による経路。
これにより既存多項式 prism 候補の標準係数射について完全忠実平坦性を証明する。
残るのはその perfectoid 商の元の A/d 上の p 完全忠実平坦性、
無限 p 冪根変数の自由基底、任意族への最終接続と元の perfectoid 基底への移送。
目標存在定理は引き続き未宣言である。
`monicPrismaticPDPerfectionCandidateEquiv_isDeltaHom` により、上記環同型の両方向が
それぞれ実際の PD 完備化 δ 構造に関して δ 射となることも証明した。
この δ 比較にも distinguished 性やモニック性・正次数・有限性は不要。
対象環の具体的な局所環構造を明示して、一般比較の両方向の δ 射性を合成している。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4297 jobs）。
専用監査も終了コード 0。新規 15 公開宣言の `assert_no_sorry` を追加し、
生成宣言を含む 1652 宣言の推移的公理依存が標準 3 公理のみであることを確認した。

### E1.17：標準生成元商の実導来比較と perfectoid 候補の p 完全忠実平坦性

`Andre/MonicPrismaticPrismBaseMap.lean` で既存候補を `polynomialPrism` として束ね、
標準係数射の δ 射性・生成元保存・イデアル像と prism 射を構成した。
`Andre/PerfectPrismMonicPrismResidue.lean` では同じ標準係数作用に関する
実 (p,d) Tor 消滅と通常係数拡大の忠実平坦性を得る。
`Andre/PerfectPrismMonicQuotientReduction.lean` では候補生成元の正則性から、
元の A/d への実導来係数拡大を標準 perfectoid 商の single に同定する。
この生成元商の比較はモニック性・正次数・有限性を要求しない。

`Andre/PerfectPrismMonicPerfectoidCompletelyFlat.lean` で (p,d) 剰余から
元の A/d 上の mod p 剰余への実基底変更比較を適用し、高次 Tor 消滅と
忠実平坦性を移した。主要公開型（namespace は `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ t, (f t).Monic)
    (hdeg : ∀ t, 0 < (f t).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    letI := (polynomialPerfectoidCandidateBaseMap P.deltaStructure P.generator f
      (OrientedPrism.isDistinguished_of_perfect P hP)).toAlgebra
    IsCompletelyFaithfullyFlat
      (Ideal.span {(p : A ⧸ Ideal.span {P.generator})})
      (PolynomialPerfectoidCandidate P.deltaStructure P.generator f
        (OrientedPrism.isDistinguished_of_perfect P hP))
```

前提は完全 prism、有限全列挙、各多項式のモニック性と正次数。
別の Tor・ghost・有界ねじれ仮定は残らず、基底射は既存候補の標準射そのもの。
BS Rem 7.15（著者版 p.62）、Thm 7.14（p.61）の原典と異なる、
PD 先行 δ 完全化の具体的比較を使う経路である。
任意族への接続、一般 perfectoid 基底への移送、無限 p 冪根変数の明示的自由基底は未完了。
目標存在定理は引き続き未宣言であり、この有限候補の結果を全体完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4303 jobs）。
専用監査も終了コード 0。新規 23 公開宣言へ `assert_no_sorry` を追加し、
生成宣言を含む 1857 宣言の推移的公理依存は標準 3 公理のみと確認した。

### E1.18：完全 prism 商上の一元・有限族の根付き拡大の存在

新規 `Andre/PerfectPrismMonicRootedExtension.lean` で、元の商上の族を同次数モニックに
持ち上げて、E1.17 の同じ標準基底射の完全忠実平坦性を適用する。
評価の自然性で元の多項式族の根方程式へ移す。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の原典とは異なる
PD 先行 δ 完全化と具体的候補比較による経路である。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem exists_finiteMonicRootedPerfectoidExtension_of_perfectPrism
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial (A ⧸ Ideal.span {P.generator}))
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    {m : ℕ} (eσ : Fin m ≃ σ) :
    ∃ (T : Type u) (_ : CommRing T)
      (φ : A ⧸ Ideal.span {P.generator} →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra;
        IsCompletelyFaithfullyFlat
          (Ideal.span {(p : A ⧸ Ideal.span {P.generator})}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0
```

`exists_monicRootedPerfectoidExtension_of_perfectPrism_fintype` は全列挙の代わりに
`[Fintype σ]` を与える同じ結論。
`exists_monicRootPerfectoidExtension_of_perfectPrism` は単一多項式 `f`、
前提 `f.Monic` と `0 < f.natDegree`、根 `ρ : T`、結論 `f.eval₂ φ ρ = 0` の一元版。
完全 prism、有限性、モニック性と正次数以外の補助仮定はない。
任意族の最終定理および一般 perfectoid 基底への移送はまだ未完了。
無限 p 冪根変数の明示的な自由基底も残り、全体の目標を完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4304 jobs）。
専用監査は終了コード 0。新規 3 公開定理の `assert_no_sorry` と、
生成宣言を含む 1862 宣言の推移的な標準 3 公理のみの依存を確認した。
3 定理の公開型を `#print` で確認（終了コード 0）。

### E1.19：一般 perfectoid 基底への有限根付き拡大の移送

新規 `Andre/MonicRootedBaseEquiv.lean` で、自己拡大・環同型の任意イデアルに関する
完全忠実平坦性と、根付き拡大の基底環同型による移送を証明する。
環同型を同じ基底上の線形同型とみなし、検証済みの E3 合成定理
`Transfinite.isCompletelyFaithfullyFlat_natCast_comp` を使う。
原典で使う Hodge–Tate 比較や新しい引用は追加しない。

新規 `Andre/FiniteMonicRootedExtension.lean` は一般の `IsIntegralPerfectoid R p` を
零枝と四条件の非零枝に分ける。非零枝では既存の
`exists_perfectoidTrialPrism` による実 PD 完備化の完全 prism 商表示を使い、
E1.18 の有限族構成に同じ次数とモニック性を保って移した多項式を入力する。
標準射の合成と `eval₂_map` で元の基底へ戻す。零枝は自己拡大で処理する。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の原典とは異なる具体的 PD 計算の経路。

主要公開型（namespace は `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem exists_finiteMonicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0
```

`exists_monicRootedPerfectoidExtension_of_finite` は全列挙を `[Finite σ]` に置き換えた同じ型。
`exists_monicRootPerfectoidExtension` は同じ基底前提で単一の
`f : Polynomial R`、`hf : f.Monic`、`hdeg : 0 < f.natDegree` を受け取り、
根を `ρ : T`、最後の結論を `f.eval₂ φ ρ = 0` とする一元版。
有限性と正次数モニック性以外に、基底の表示・p 正則性・ねじれなし・平坦性の補助仮定はない。
一般基底への移送はこの有限版で解消した。任意族への接続と無限 p 冪根変数の明示的自由基底は残る。
最終目標 `exists_monicRootedPerfectoidExtension` は引き続き未宣言であり、全体完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4311 jobs）。
新規 6 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 1868 宣言の推移的公理依存は標準 3 公理のみ。
存在定理 3 本の公開型も `#print` で確認した（終了コード 0）。

### E1.20：任意モニック族の有界深さ有限部分族と実残余評価の Tor 消滅

新規 `Andre/MonicPrismaticFiniteSubfamilyTor.lean` は、任意添字型 σ 内の有限部分族
`T : Set σ` と全列挙 `s : Fin m ≃ T` を扱う。
元の無限族の自由 δ 環を、補集合の自由 δ 変数を係数とする部分族の自由 δ 環に分離する
既存の一般構成を再利用する。
`monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular` の任意有限部分族の初項入力を
`deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular` へ渡し、全有界 δ 深さの
Koszul 分解と対応する実源グラフ商の高次 Tor 消滅を得る。

新規 `Andre/MonicPrismaticBoundedSupportTor.lean` は、元の評価図式
`deltaDivisionBoundedSupportModuleDiagram`（添字 Finset (σ × ℕ)）の全段にその消滅を適用。
同じ図式と実 TorAlg 関手に対する既存の `torAlg_preservesFinsetColimits` により、
全評価環の消滅 `monicPrismaticEvaluation_tor_subsingleton` と、通常 Tor 比較・対称性による
`monicPrismaticBoundedSupportResidueEval_torVanishing` を得る。
中間補題 `monicPrismaticEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit` の
実図式の保存仮定は、これら二つの公開入口では残さない。

新規 `Andre/MonicPrismaticArbitraryResidue.lean` の主要公開型は、以下の記法で示す。
`P₁ := MvPolynomial σ A`、`E₁ := polynomialRankOneDeltaStructure σ D`、
`L₁ := RelativeFreeDeltaRing (R := P₁) σ`、
`c₁ := fun t : σ => monicRelation (f t) t`、
`K₁ := Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}`、
`ψ₁ := (Ideal.Quotient.mk K₁).comp (deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d))`、
`β₁ := deltaDivisionSourceEval E₁ c₁`、`Mψ := baseChangeScalarModule ψ₁` とする。

```lean
def monicPrismaticArbitraryResidueSourceDerivedIso
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (boundedAboveDerivedBaseChange β₁).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of P₁ (DeltaAdjoinDivisionResidue E₁ (MvPolynomial.C d) c₁))
```

同じ前提で `monicPrismaticBoundedSupportResidueEval_torVanishing` の結論は
`scalarExtensionTorVanishing β₁ Mψ`。
全添字型の有限性、多項式の正次数、余極限交換の追加仮定は不要。
実係数射と標準導来 augmentation を保持し、通常残余テンソルの比較と合成する。
BS Rem 7.15（著者版 p.62）の原典とは異なる具体的 PD 計算の経路。
残るのは、この任意族の実残余比較を元の A/(p,d) 上の完備化・完全化の連鎖へ接続して
最終存在定理を公開する工程、および無限 p 冪根変数の明示的自由基底。
任意族の最終存在定理は未宣言であり、全体完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4337 jobs）。
新規 8 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 1988 宣言の推移的公理依存は標準 3 公理のみ。
主要な全評価 Tor 消滅と実導来評価同型の公開型を `#print` で確認した（終了コード 0）。

### E1.21：任意族の実係数剰余と逐次 p,d 完備化後の剰余

新規 `ArbitraryMonicPrismaticCoefficientReduction.lean` は E1.20 の全評価源比較を
一般結合子と右因子の商比較へ接続し、実三因子還元を同じ raw (p,d) 剰余の single に同定。
`ArbitraryMonicPrismaticQuotientDerived.lean` は全射商での係数作用の降下、
H⁰ の商線形比較、実商対象の非零次数消滅・純性・single 比較を任意族に一般化する。
候補環や元の係数射の定義は既存のまま使う。
`ArbitraryMonicPrismaticQuotientFlat.lean` はこの H⁰ 比較を元の係数商へ制限し、
任意モニック族の raw 剰余の忠実平坦性へ移す。
`ArbitraryMonicPrismaticPDReduction.lean` は二重多項式源の一般正方形比較を使って
元の A/(p,d) に沿う実還元の離散性と H⁰ 忠実平坦性を得る。
`ArbitraryMonicPrismaticIteratedResidue.lean` は p,d の個別正則性による既存の単位比較を用い、
逐次 p,d 実導来完備化後にも同じ実剰余比較を与える。
原典の Prop 7.11 を使う証明とは異なる、BS Rem 7.15（著者版 p.62）の具体的 PD 計算の経路。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat_arbitrary
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))).obj
          (MonicPrismaticSourceIteratedPDCompletion D d f)).obj)
```

`monicPrismaticSourceIteratedPDResidue_homology_isZero_arbitrary` は同じ入力から正次数条件を外し、
`(i : ℤ) (hi : i ≠ 0)` を加えた型で、上記対象の i 次ホモロジーが `IsZero` であると述べる。
`monicPrismaticSourceIteratedPDResidueIso_arbitrary` とその `_unit_arbitrary` は
実 raw 剰余への比較と元の標準完備化単位の像の公式を保持する。
有限全列挙・有限性の仮定は全て外した。p 正則性、d 正則性、δ(d) 単元性は明示的に残り、
完全 prism 上では次工程で既存の性質から供給する。
残るのは任意族の完備化源の離散性、raw PD・完全化・候補環比較への接続、
最終存在定理の公開、および無限 p 冪根変数の明示的自由基底。
最終目標はまだ未宣言であり、全体完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4342 jobs）。
新規 18 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2296 宣言の推移的公理依存は標準 3 公理のみ。
主要な逐次完備化後の実剰余の公開型 2 本を `#print` で確認した（終了コード 0）。

### E1.22：任意族の実源の離散性から既存 perfectoid 候補の p 完全忠実平坦性へ

新規 `ArbitraryMonicPrismaticCanonicalPowerResidue.lean` と
`ArbitraryMonicPrismaticSourcePowerInputs.lean` は、E1.21 の実剰余比較を
正の生成元冪商へ移し、標準冪零還元と G9 用の実入力を任意族について供給する。
`ArbitraryPerfectPrismMonicSourceDiscrete.lean` は完全 prism の生成元冪商の p ねじれ上界を使い、
同じ逐次 p,d 完備化源が離散的となることを示す。
`ArbitraryPerfectPrismMonicRawPDCompletelyFlat.lean` は既存の任意族に対する実 H⁰ 比較を再利用し、
raw PD 環の元の A 上の実 (p,d) 還元の離散性・H⁰ 忠実平坦性・完全忠実平坦性を得る。
`ArbitraryPerfectPrismMonicPDPerfectionInputs.lean` は既存の一般 δ 代数の定理へその実入力を渡し、
PD 環の δ 完全化と再実 PD 完備化の完全忠実平坦性を示す。
`ArbitraryPerfectPrismMonicPrismCompletelyFlat.lean` は、任意族について既に証明済みの
具体的係数射を保つ環・加群同型で、既存多項式 prism 候補の標準係数射へ移す。
`ArbitraryPerfectPrismMonicPrismResidue.lean` と
`ArbitraryPerfectPrismMonicPerfectoidCompletelyFlat.lean` は標準生成元商の実導来比較を使い、
元の A/d 上の p 完全忠実平坦性へ移す。
どの段も族全体の有限性を仮定しない。原典と異なる BS Rem 7.15（著者版 p.62）の
PD 先行構成と具体的係数比較による経路である。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat_arbitrary
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ t, (f t).Monic)
    (hdeg : ∀ t, 0 < (f t).natDegree) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    letI := (polynomialPerfectoidCandidateBaseMap P.deltaStructure P.generator f
      (OrientedPrism.isDistinguished_of_perfect P hP)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {P.generator})})
      (PolynomialPerfectoidCandidate P.deltaStructure P.generator f
        (OrientedPrism.isDistinguished_of_perfect P hP))
```

`perfectPrismMonicSource_pure_arbitrary` は同じ完全 prism・正次数モニック族を前提に、
`(MonicPrismaticSourceIteratedPDCompletion P.deltaStructure P.generator f).obj` の
`IsGE 0 ∧ IsLE 0` を述べる。外部の ghost・有界ねじれ・Tor・完備化離散性の仮定は残らない。
次はこの標準候補をモニック lift と一般基底への移送へ接続する存在定理の公開。
無限 p 冪根変数の明示的な自由基底も残る。全体完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4350 jobs）。
新規 35 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2705 宣言の推移的公理依存は標準 3 公理のみ。
候補標準基底射の完全忠実平坦性と実源純性の公開型を `#print` で確認した（終了コード 0）。

### E1.23：指定された任意モニック族の根付き perfectoid 拡大の公開

`ArbitraryPerfectPrismMonicRootedExtension.lean` は、完全 prism 商上の任意の正次数モニック族を
同次数モニックに lift し、E1.22 の同じ標準候補の p 完全忠実平坦性を適用する。
評価の自然性で元の商上の多項式族の根方程式を得る。
`MonicRootedPerfectoidExtension.lean` は一般の整 perfectoid 基底を零枝と非零枝に分け、
非零枝の完全 prism 商表示と基底環同型による移送を適用する。
零枝は自己拡大を使う。全ての台環と根の添字型を Type u に保つ。

公開型（namespace は `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem exists_monicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0
```

正次数の仮定は元の型の f=1 の問題に対してユーザーが承認した訂正であり、
それ以外の補助仮定、族全体の有限性、基底の表示・p 正則性・ねじれなしは要求しない。
`exists_monicRootedPerfectoidExtension_of_perfectPrism` は同じ型で、
基底 R を完全 prism P の商 A/(P.generator)、基底の perfectoid 仮定を
`P.deltaStructure.IsPerfect` に置き換えた入口。
集約ファイルから公開し、既存のルート import は一行のまま保つ。

BS Thm 7.14（著者版 p.61）の第一段であり、Rem 7.15（p.62）に沿う別経路である。
原典の Prop 7.11・Hodge–Tate 比較を使う証明とは異なり、具体的 δ 除算、
有界深さ有限部分族の実余極限、実 p,d 完備化、PD 先行 δ 完全化の係数射を保つ比較を使う。
新しい sorry・axiom・引用は導入せず、BS Cor 8.12 も宣言・使用しない。

任意族の一段拡大という指定出力は得たが、依頼全体をまだ完成とは数えない。
補足計算として要求された無限 p 冪根変数の明示的自由基底、およびその上のモニック冪商の
自由性と原典の具体的 pd 表示との同定の範囲を、要求ごとの最終監査で確認する必要がある。
既存の Inputs/AndreFlatness.lean と他レーンのファイルは編集しない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4352 jobs）。
新規 2 公開定理の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2709 宣言の推移的公理依存は標準 3 公理のみ。
存在定理 2 本の公開型と `#print axioms` を確認（終了コード 0）。
指定出力の任意族版そのものの公理依存も propext・Classical.choice・Quot.sound のみ。

### E1.24：無限 p 冪根多項式環の具体的指数と単項式基底

`Andre/PowerRootExponents.lean` で
`powerRootExponentMonoid p hp := {q : ℚ | ∃ n a : ℕ, q * p^n = a}` を
実加法部分モノイドとして構成した（`hp : 0 < p`）。全指数の非負性と
`q = a / p^n` の表示を証明する。
`powerRootExponentSplit` は指数を自然数部分と 1 未満の指数に一意に分解し、
`powerRootExponentSplit_nat_add` は自然数を足すと小数部分を保ち整数部分だけ増える公式を与える。

`Andre/PowerRootPolynomial.lean` はその加法モノイド環
`PowerRootPolynomial R p hp := AddMonoidAlgebra R (powerRootExponentMonoid p hp)` を用いる。
変数 `powerRootPolynomialVariable R p hp n` は指数 1/pⁿ・係数 1 の単項式で、
隣接する変数の p 冪関係を満たす。全単項式はある段の変数の冪と係数の積として表され、
全変数の R 上の adjoin は環全体となる。
既存加法モノイド環の基底から、具体的な単項式基底と係数環上の自由性を得る。
BS Rem 7.15（著者版 p.62）の未完備の無限 p 冪根多項式環 P の自由性の具体的計算。

主要公開型（namespace は `SerrePositivity.BhattScholze.Andre`）：

```lean
def powerRootPolynomialBasis
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) :
    Module.Basis (powerRootExponentMonoid p hp) R (PowerRootPolynomial R p hp)

theorem powerRootPolynomial_free
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) :
    Module.Free R (PowerRootPolynomial R p hp)

theorem powerRootPolynomialVariable_pow
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) (n : ℕ) :
    powerRootPolynomialVariable R p hp (n + 1) ^ p = powerRootPolynomialVariable R p hp n
```

基底の値は `AddMonoidAlgebra.single q 1`。
p の素数性、係数環の標数・非零性・被約性は要求しない。
原典の P=R/ϖ[Y¹⸍ᵖ∞] には係数環 R を R/ϖ として適用する。
この環は未完備の具体的単項式モデルであり、prismatic envelope やその Frobenius 引戻しとの
同定を新たに主張するものではない。
残る計算は、通常多項式環上の小数指数基底とモニック冪商の自由性、
原典の具体的 pd 包との同定の補完。指定出力の存在定理は E1.23 で証明済みだが、
これらの残りを終えるまで依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4355 jobs）。
新規 20 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2742 宣言の推移的公理依存は標準 3 公理のみ。
指数分解・具体的基底・自由性・生成の公開型を `#print` で確認した（終了コード 0）。

### E1.25：小数指数基底、モニック冪商、無限変数内の分冪表示環

`PowerRootPolynomialCoordinates.lean` は、指数の自然数・小数部分への一意分解を使い、
単項式座標を小数指数ごとの通常多項式に変換する元の係数環上の線形同型を構成した。
通常変数を Y₀ に送る標準評価射と、その単項式上の式を明示する。
`PowerRootPolynomialFractionBasis.lean` は自然数指数の加法の公式を使って、
同じ座標が通常多項式環上でも線形であることを証明する。
標準評価射の toAlgebra に関して、小数指数の係数 1 の単項式が具体的自由基底となる。

`PowerRootMonicQuotient.lean` は、この基底を通常多項式商へ基底変更し、
実拡張イデアル商とテンソルの標準同型で戻した。
元の係数作用と商環作用のスカラー塔を代表元上で検証し、通常モニック商の冪基底と合成する。
結果の基底の添字は `Fin f.natDegree × PowerRootFraction p hp`。
正次数の場合、零係数環を分けて非空基底から忠実平坦性も得る。
モニック f の像は、通常多項式環上の自由性による平坦性で非零因子となる。

`PowerRootMonicPDFlat.lean` は標数 p の場合に、同じ実 fᵖ 商上の分冪表示環の
自由性・忠実平坦性を合成し、無限 p 冪根変数内の分冪表示環の元の係数環上の性質を証明した。
BS Rem 7.15（著者版 p.62）の具体的通常代数計算であり、原典の Prop 7.11 による経路は使わない。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
def powerRootPolynomialFractionBasis
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Basis (PowerRootFraction p hp) R[X] (PowerRootPolynomial R p hp)

def powerRootPolynomialQuotientBasis
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) (f : R[X]) (hf : f.Monic) :
    Module.Basis (Fin f.natDegree × PowerRootFraction p hp) R
      (PowerRootPolynomialQuotient R p hp f)

theorem powerRootPolynomialPowerQuotient_free
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p) (f : R[X]) (hf : f.Monic) :
    Module.Free R (PowerRootPolynomialQuotient R p hp (f ^ p))

theorem powerRootMonicDPPresentation_free
    (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
    (hprime : p.Prime) (hpR : (p : R) = 0) (f : R[X]) (hf : f.Monic) :
    Module.Free R (PrincipalDPPresentation (PowerRootPolynomial R p hp)
      (powerRootPolynomialBaseMap R p hp f))
```

`PowerRootPolynomialQuotient` の定義イデアルは f の標準評価像の主イデアルに一致する。
従って fᵖ に適用した上記商は P/(f(Y₀)ᵖ) そのもの。
`powerRootPolynomialPowerQuotient_faithfullyFlat` は同じ入力に `0 < f.natDegree` を加え、
結論を `Module.FaithfullyFlat R (PowerRootPolynomialQuotient R p hp (f ^ p))` とする。
`powerRootMonicDPPresentation_faithfullyFlat` も上記分冪表示環の入力に同じ正次数を加えた型。
自由性だけには正次数・係数環の非零性を要求しない。多項式商の結果には標数の仮定も不要。
残る要求は、分冪表示環を実 pd 包・具体的切断多項式表示に同定し、
原典の prismatic envelope の Frobenius 引戻しの計算と照合する部分。
指定出力の存在定理は E1.23 で証明済みだが、依頼全体の完成とはまだ数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4359 jobs）。
新規 23 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2808 宣言の推移的公理依存は標準 3 公理のみ。
主要な基底・冪商の自由性と忠実平坦性・分冪表示環の自由性と忠実平坦性の
公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.26：素数次数シフトと可算切断多項式商からの全射

新規 `Andre/DividedPowerPrimeShift.lean` は任意の可換係数環 A について、
標準分冪基底の γₙ を γₚₙ へ送る A 線形写像を構成する。
p が A 内で零なら、Lucas の二項係数合同
`Choose.choose_mul_mul_modEq_choose_nat` と双線形写像の基底上の比較から積保存を証明し、
A 代数射 `dividedPowerPrimeShift` として束ねる。
一次分冪生成元の p 乗消滅をこの射で順に移して、全 γₚⁱ の p 乗が零であることを得た。
また、標準分冪基底の独立性を単射な指数写像 n↦pn に制限することで、
この次数シフト自体の単射性も証明する。
この次数シフトは通常の Frobenius とは異なる射であり、prismatic Frobenius との同定は主張しない。

新規 `Andre/DividedPowerPrimeGenerators.lean` は、素数冪次数の分冪で生成した部分代数が
次数シフトで保たれることを示す。次数 n の p による商・剰余を使う強帰納と、
p 未満の階乗の単元性により、全ての標準分冪 γₙ の所属を得る。
それらの A 線形生成から、素数冪次数の分冪が全一元分冪代数を生成することを証明した。
各生成元の p 乗が零なので、可算切断多項式商からの標準 A 代数射を構成し、その全射性を証明した。
関係イデアルが純粋に全変数の p 乗で生成される公式と、商からの射の変数上の外延性を付ける。
BS Rem 7.15(1)（著者版 p.62）の具体的切断表示に至る計算。原典の Prop 7.11 は使わない。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
def dividedPowerPrimeShift
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    DividedPowerAlgebra A A →ₐ[A] DividedPowerAlgebra A A

theorem dividedPowerPrimePower_pow_zero
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (n : ℕ) :
    DividedPowerAlgebra.dp A (p ^ n) (1 : A) ^ p = 0

def dividedPowerPrimeTruncatedEval
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] DividedPowerAlgebra A A

theorem dividedPowerPrimeTruncatedEval_surjective
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Surjective (dividedPowerPrimeTruncatedEval (A := A) p hp)
```

ここで `DividedPowerPrimeTruncatedAlgebra` は
`MvPolynomial ℕ A ⧸ Ideal.span (Set.range fun i : ℕ => (MvPolynomial.X i)^p)` と同じ実商。
変数 i の評価値は γₚⁱ。係数環の非零性や CharP インスタンスは要求しない。
残るのはこの評価射の単射性、γ₁=f を課した係数商との比較、実 pd 包と
prismatic envelope の Frobenius 引戻しとの同定。全射を同型とは数えず、
指定出力の存在定理以外の残る計算があるため依頼全体も未完了とする。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4362 jobs）。
新規 18 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2851 宣言の推移的公理依存は標準 3 公理のみ。
次数シフト・p 乗消滅・シフト単射性・切断評価射とその全射性の公開型 5 本を
`#print` で確認した（終了コード 0）。

### E1.27：最初の切断変数と次数シフト側のテンソル分解

新規 `Andre/DividedPowerPrimeTensor.lean` は、可換係数環 A、素数 p、
係数環内の等式 `(p : A) = 0` の下で、次の A 代数同型を構成する。

```lean
def dividedPowerPrimeTensorEquiv
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    AdjoinRoot ((Polynomial.X : Polynomial A) ^ p) ⊗[A]
      DividedPowerAlgebra A A ≃ₐ[A] DividedPowerAlgebra A A
```

順射 `dividedPowerPrimeTensorMap` は、純テンソル c⊗d を
`rankOneDPTruncatedMap` による c の像と `dividedPowerPrimeShift` による d の像の積に送る。
`dividedPowerPrimeTensorMap_bijective` はこの射の全単射性を主張する。
証明は、切断多項式環の標準冪基底と標準分冪基底のテンソル基底を、
既存の次数ブロック基底へ送る線形同型と比較する。零係数環は別枝の自明性で処理するので、
非零性・追加の平坦性・CharP インスタンスは前提に残らない。
BS Rem 7.15(1)（著者版 p.62）の可算切断多項式表示に向けた一段の分解であり、
通常の Frobenius のテンソル分解や prismatic Frobenius との同定は主張しない。
可算切断評価全体の単射性、γ₁=f を課した商の比較、実 pd 包および
prismatic envelope の Frobenius 引戻しとの同定は引き続き未完了。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4363 jobs）。
新規 5 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2871 宣言の推移的公理依存は標準 3 公理のみ。
テンソル評価射・全単射性・代数同型の公開型 3 本を `#print` で確認した（終了コード 0）。

### E1.28：有限テンソル段の独立性から可算切断表示の同型へ

新規 `Andre/DividedPowerPrimeFiniteTensor.lean` は、切断多項式環
C=A[X]/(Xᵖ) の有限反復テンソル段（零段 A、次段 C⊗前段）を構成する。
C のモニック商としての自由性から、任意の単射 B→Γ_A(A) のテンソル化は単射。
E1.27 のテンソル分解と合成して、全有限段の分冪評価の単射性を得た。
各段の変数は p 乗が零で、その評価は同じ番号 i の γₚⁱ である。

新規 `Andre/DividedPowerPrimeFiniteUniversal.lean` は、これらの有限段について
p 乗が零となる任意の有限元族への普遍射、変数の評価公式、変数上の外延性を証明する。
新規 `Andre/DividedPowerPrimeFinitePresentation.lean` は有限切断多項式商との
具体的な互いに逆な射を構成し、係数代数同型および有限切断評価の単射性を得る。
表示の普遍性と同型には、p の素数性も標数の仮定も不要。

新規 `Andre/DividedPowerPrimePresentation.lean` は、可算切断商の任意の元が
ある有限初期変数商から来ることを代表多項式の変数集合の上限により証明する。
有限・可算評価の互換性と有限評価の単射性から可算評価の単射性を得る。
E1.26 の全射性と合わせ、素数 p が A 内で零となる仮定の下で次の係数代数同型を構成した
（namespace `SerrePositivity.BhattScholze.Andre`）。

```lean
theorem dividedPowerPrimeTruncatedEval_injective
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeTruncatedEval (A := A) p hp)

def dividedPowerPrimeTruncatedEquiv
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p ≃ₐ[A] DividedPowerAlgebra A A
```

左辺は実際の商 `MvPolynomial ℕ A ⧸ Ideal.span (Set.range fun i => (MvPolynomial.X i)^p)`。
`dividedPowerPrimeTruncatedEquiv_X` により変数 i は γₚⁱ、特に最初の変数は γ₁ に対応する。
係数環の非零性・追加の平坦性・CharP インスタンスは不要。
BS Rem 7.15(1)（著者版 p.62）の切断表示の自由分冪代数側の計算であり、
原典の Prop 7.11 を使わない有限テンソル分解・有限支持による経路である。
残るのは γ₁=f を課した商の係数商との比較、実 pd 包の構造・普遍性、
prismatic envelope の Frobenius 引戻しとの同定である。
指定出力の存在定理は E1.23 で証明済みだが、本依頼全体は未完了。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4370 jobs）。
新規 27 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2950 宣言の推移的公理依存は標準 3 公理のみ。
有限段の評価単射性・表示同型・有限支持・可算評価単射性と代数同型・変数公式の
公開型 7 本を `#print` で確認した（終了コード 0）。

### E1.29：γ₁=y の一次関係商の明示的な係数商上の切断表示

新規 `Andre/DividedPowerPrimeUniversal.lean` は、任意の p 乗零元族への
可算切断商の普遍射を構成する。素数 p が A 内で零となる場合には、
自由一元分冪代数およびその一次関係商からの係数代数射が、
素数冪次数の分冪の値だけで一意に決まることも証明した。

新規 `Andre/PrincipalDPTruncatedPresentation.lean` は、係数商 A/(yᵖ) 上の
可算切断商を `PrincipalDPTruncatedPresentation p y` として定義する。
自由分冪側の最初の切断変数を係数 y の像、後続変数を残りの切断変数へ送る。
この写像が γ₁=y を満たすので一次関係商へ降りる。
逆射は切断変数 i を次数 p^(i+1) の分冪の標準像に送る。
係数商作用は既存の `principalDPQuotientAlgebra` とそのスカラー塔を明示して使い、
元の A 作用へ制限する。両合成の恒等性を素数冪生成元と切断変数で確認した。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
def principalDPTruncatedEquiv
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (y : A) :
    PrincipalDPPresentation A y ≃ₐ[A] PrincipalDPTruncatedPresentation p y

def principalDPTruncatedQuotientAlgEquiv
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos hp y
    PrincipalDPPresentation A y ≃ₐ[A ⧸ Ideal.span {y ^ p}]
      PrincipalDPTruncatedPresentation p y

theorem principalDPPresentation_free_via_truncated
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos hp y
    Module.Free (A ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation A y)
```

右辺の表示環は実商
`MvPolynomial ℕ (A ⧸ Ideal.span {y ^ p}) ⧸ Ideal.span (Set.range fun i => (MvPolynomial.X i)^p)`。
`principalDPTruncatedEquiv_generator_succ` により γₚⁱ⁺¹ の像は変数 i。
通常環の表示と自由性には y の非零因子性は不要であり、零係数商も含む。
BS Rem 7.15(1)（著者版 p.62）の明示表示の通常環側の計算で、
原典の Prop 7.11 を使わない有限テンソル分解・普遍射による経路である。
この一般性で `PrincipalDPPresentation` を実 pd 包とは呼ばない。
非零因子入力での実分冪構造と pd 包の普遍性、prismatic envelope の
Frobenius 引戻しとの同定はなお未完了。指定出力の存在定理は E1.23 で証明済みだが、
依頼全体は完成と数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4372 jobs）。
新規 22 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 2998 宣言の推移的公理依存は標準 3 公理のみ。
A 代数同型・既存係数商上の代数同型・後続生成元公式・明示表示経由の自由性の
公開型 4 本を `#print` で確認した（終了コード 0）。

### E1.30：実 mod p 分冪構造と正則 δ 持ち上げの場合の pd 普遍性

新規 `Andre/PrimeDividedPowerQuotient.lean` は、p 正則・p 局所な可換環の
分冪イデアルが p を含めば (p) は分冪安定であり、構造が実 mod p 商へ降りることを証明する。
n! の p 付値が正の n より小さいことと階乗恒等式を用いて γₙ(p) の p 可除性を示し、
p 冪因子の消去には p 正則性、残りの階乗因子の消去には p 局所性を使う。
商の分冪値の公式と、標準商射が分冪射であることも公開した。

新規 `Andre/FactorialModPrimeDividedPowers.lean` は、既存の階乗部分環の大きい
p 除算可能イデアルの分冪構造をこの方法で mod p に降ろす。
元の正次数イデアルの像は分冪安定なので、そこへ制限して実分冪構造を得る。
この段階では係数環の p 正則性も入力族の正則性も不要で、部分環自体の p 正則性を使う。
正次数イデアルの p 飽和性は仮定しない。入力元の分冪値は全階乗生成元の剰余に一致する。

新規 `Andre/RegularPrincipalModPrimeDividedPowers.lean` は、p 正則・p 局所な δ 環 A の
元 y が mod p で非零因子である場合に、既存の `regularPrincipalDPFactorialModPEquiv` により
実構造を `PrincipalDPPresentation (A/(p)) (y mod p)` へ移す。
構造のイデアルは全正次数標準生成元の span `principalDPPositiveIdeal` と同定する。
入力元の n 次分冪が n 次標準生成元に一致する公式も証明した。

新規 `Andre/PrincipalDPPositiveUniversal.lean` は、正次数イデアルの分冪構造と
上記の値の公式から、既存の `principalDPEval` の分冪保存と一意存在を証明する。
新規 `Andre/RegularPrincipalModPrimeUniversal.lean` は、実際に構成した構造と公式を渡して
任意の分冪標的への普遍性を得る。標的には p ねじれ・正則性・δ 構造・完備性の仮定を置かない。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
def regularPrincipalModPrimeDividedPowers
    {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    DividedPowers (principalDPPositiveIdeal (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
```

`existsUnique_regularPrincipalModPrimeDPMorphism` はこの同じ持ち上げの前提の下で、
任意の可換環 B と `Algebra (A/(p)) B`、任意の分冪イデアル `(I,Ht)`、
y の係数像が I に属する仮定に対して、上記一次関係商から B への
`A/(p)` 代数射 F で実分冪構造を保つものの一意存在を主張する。
分冪構造やその標準値そのものを仮定として残してはいない。

BS Rem 7.15(1)（著者版 p.62）の pd 包の計算を階乗部分環・mod p 降下で進める経路であり、
原典の Prop 7.11 を使用しない。任意の正標数正則入力を既存の δ 持ち上げへ
結び付ける適用と、prismatic envelope の Frobenius 引戻しとの同定はなお未完了。
持ち上げを明示した今回の結果だけで依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4416 jobs）。
新規 20 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3054 宣言の推移的公理依存は標準 3 公理のみ。
一般 mod p 分冪降下・階乗部分環の実構造・一次関係商の実構造・入力元の値・
具体的な正則持ち上げの普遍性の公開型 5 本を `#print` で確認した（終了コード 0）。

### E1.31：モニック入力・完全 prism への実 mod p 分冪包の適用

新規 `Andre/MonicModPrimePDEnvelope.lean` は、p 正則・p 局所 δ 係数環 A 上で
モニック多項式 f を独立変数 s で評価した入力について、E1.30 の実構造と普遍性を適用する。
`monicPolynomialRing_primeRegular` は多項式環の自由性から p 正則性を、
`monicPolynomialRing_primeLocal` は係数射から p 局所性を供給する。
関係式の mod p 正則性は既存の `monicRelation_modP_isSMulRegular` による。
そのため入力の mod p 正則性は公開定理の追加仮定として残らない。
`monicModPrimePDDividedPowers` と入力元上の標準分冪値の公式、
`existsUnique_monicModPrimePDMorphism` を公開する。モニック f の正次数はここでは不要。

新規 `Andre/PerfectPrismMonicModPrimePDEnvelope.lean` は、完全 prism の p 完備性から
p の Jacobson 根基への所属を取り出し、Bezout 等式を用いる
`primeLocal_of_prime_mem_jacobson` により p 局所性を供給する。
p 正則性は完全 δ 構造の既存結果を使う。
`perfectPrismMonicModPrimeDividedPowers` はこれらを内部で供給した実分冪構造である。
`existsUnique_perfectPrismMonicModPrimePDMorphism` は同じ構造の普遍性を主張する。

主要公開定理の正確な形は次の通り（namespace `SerrePositivity.BhattScholze.Andre`）。
ここで `B := MvPolynomial σ A`、`Q := B ⧸ Ideal.span {(p : B)}`、
`bar := Ideal.Quotient.mk (Ideal.span {(p : B)})` とする。

```lean
theorem existsUnique_perfectPrismMonicModPrimePDMorphism
    {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : σ)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (monicRelation f s)) ∈ I) :
    ∃! F : MonicModPrimePDEnvelope (p := p) f s →ₐ[Q] T,
      (perfectPrismMonicModPrimeDividedPowers P hP f hf s).IsDPMorphism Ht F.toRingHom
```

`MonicModPrimePDEnvelope f s` の実台環は `PrincipalDPPresentation Q (bar (monicRelation f s))`。
その正次数イデアルは全正次数標準分冪生成元の span。
同じ台環について `monicModPrimePDEnvelope_truncatedEquiv` は、既存の
`principalDPQuotientAlgebra` が指定する係数商 `Q/(bar(f(s))^p)` 上の代数同型を与える。
終域はこの係数商上の実可算切断多項式商で、`monicModPrimePDEnvelope_quotient_free` は
同じ係数商作用の下での自由性を明示表示により証明する。

BS Rem 7.15(1)（著者版 p.62）の実 pd 包の計算を通常多項式変数に適用した段階。
原典の Prop 7.11 は使わず、階乗部分環の mod p 降下と明示切断表示を用いる。
無限 p 冪根変数への移行、対象の R/ϖ 係数との比較、および prismatic envelope の
Frobenius 引戻しとの同定はなお未完了。今回の通常多項式変数での適用だけで
依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4418 jobs）。
新規 13 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3086 宣言の推移的公理依存は標準 3 公理のみ。
モニック入力と完全 prism の実分冪構造・完全 prism の普遍性・係数商上の切断同型・
自由性の公開型 5 本を `#print` で確認した（終了コード 0）。

### E1.32：無限 p 冪根多項式環の実 Frobenius 持ち上げと δ 構造

新規 `Andre/PowerRootPolynomialDelta.lean` は既存の実単項式モデル
`PowerRootPolynomial A p hp` の台環上で、係数に元の δ 環の Frobenius を、
指数に p 倍を作用させる環自己射 `powerRootPolynomialFrobenius` を構成する。
単項式・係数・全根変数上の値をそれぞれ証明した。

実 mod p 商でこの射が通常の p 乗と一致することを加法モノイド環の帰納法で示す。
加法の場合は素数の二項係数公式、係数倍の場合は元の δ 環の Frobenius 恒等式を使う。
零環を含めるため CharP インスタンスは仮定しない。
係数環で p が正則なら単項式基底の自由性で同じ環の p 正則性を得るので、
既存の `DeltaStructure.existsUnique_of_mod_p` により指定した Frobenius を持つ δ 構造を構成できる。

主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
def powerRootPolynomialDelta
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    DeltaStructure p (PowerRootPolynomial A p (Fact.out : p.Prime).pos)

theorem powerRootPolynomialDelta_coeff_isDeltaHom
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    D.IsDeltaHom (powerRootPolynomialDelta p hpA D)
      (algebraMap A (PowerRootPolynomial A p (Fact.out : p.Prime).pos))

theorem powerRootPolynomialDelta_variable
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) (n : ℕ) :
    (powerRootPolynomialDelta p hpA D).delta
      (powerRootPolynomialVariable A p (Fact.out : p.Prime).pos n) = 0
```

`existsUnique_powerRootPolynomialDelta` は同じ台環の指定した Frobenius を持つ構造の一意存在を主張する。
係数の δ 互換性は Frobenius の互換性と終域の p 正則性から得る。
根変数の δ の零性は Frobenius が p 乗になる式を p 正則性で消去して得る。
BS Rem 7.15（著者版 p.62）の無限根多項式上の実 pd 計算への持ち上げであり、
原典の Prop 7.11 を使用しない。
この環上のモニック入力の実 mod p 正則性と E1.30 の分冪包の構成への適用、
R/ϖ 係数との比較、prismatic envelope の Frobenius 引戻しとの同定はなお未完了。
δ 構造ができたことだけで依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4419 jobs）。
新規 12 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3111 宣言の推移的公理依存は標準 3 公理のみ。
Frobenius の実 mod p 一致・δ 構造の一意存在・実構造・係数射の δ 互換性・
全根変数の δ 零性の公開型 5 本を `#print` で確認した（終了コード 0）。

### E1.33：無限根環の実 mod p 係数比較とモニック入力の実 pd 包

新規 `Andre/PowerRootPolynomialModPrime.lean` は、同じ実指数モノイドについて
`PowerRootPolynomial A p hp /(p)` と `PowerRootPolynomial (A/(p)) p hp` の環同型
`powerRootPolynomialModPrimeEquiv` を構成する。
係数商射の全射性は係数の有限支持の持ち上げから得る。
核の元は全係数が p で割れるため、各単項式を p の倍数に書いて足し戻し、
核が環内の p 主イデアルそのものであることを証明する。
係数・変数・通常多項式評価の互換性も証明した。
この比較でモニック性を係数商へ移し、既存の無限根環上の正則性から
`powerRootPolynomial_monic_mod_prime_regular` を得る。
この実 mod p 正則性には係数環の p 正則性や p の素数性すら不要で、正値性のみを使う。

新規 `Andre/PowerRootMonicModPrimePDEnvelope.lean` は、E1.32 の実 δ 構造と
自由性による p 正則性、係数の p 局所性、上記の入力の mod p 正則性を供給し、
無限根環上のモニック入力へ E1.30 の実分冪構造と普遍性を適用する。
完全 prism の場合は全ての補助入力を内部で供給した構造・普遍性も公開した。
入力元 `powerRootMonicPDInput p f` は既存の `powerRootPolynomialBaseMap` による f の評価そのもの。
分冪構造の型照合で多項式評価の内部展開が繰り返されるのを防ぐため irreducible とし、
定義を明示展開する mod p 正則性補題を介して使う。
分冪値の公式は構造の定義を一段だけ展開し、`with_reducible` で既存定理を適用して証明する。
計算量上限を増やす設定は残していない。

主要公開定理の正確な形（namespace `SerrePositivity.BhattScholze.Andre`）。
ここで `hp := (Fact.out : p.Prime).pos`、`P := PowerRootPolynomial A p hp`、
`Q := P ⧸ Ideal.span {(p : P)}`、`bar := Ideal.Quotient.mk (Ideal.span {(p : P)})`、
`y := powerRootMonicPDInput p f` とする。

```lean
theorem existsUnique_perfectPrismPowerRootMonicModPrimePDMorphism
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar y) ∈ I) :
    ∃! F : PowerRootMonicModPrimePDEnvelope p f →ₐ[Q] T,
      (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf).IsDPMorphism Ht F.toRingHom
```

台環は `PrincipalDPPresentation Q (bar y)`、分冪イデアルは全正次数標準生成元の span。
入力元の n 次分冪が n 次標準生成元になる公式も証明済み。
同じ台環の `powerRootMonicModPrimePDEnvelope_truncatedEquiv` は、既存の
`principalDPQuotientAlgebra` が指定する `Q/((bar y)^p)` 上の可算切断表示への代数同型。
`powerRootMonicModPrimePDEnvelope_quotient_free` は同じ作用の自由性を与える。
分冪包の構成にモニック性を使うが、台環の表示・この係数商上の自由性自体には不要。

BS Rem 7.15(1)（著者版 p.62）の無限根変数を含む実 pd 計算であり、
原典の Prop 7.11 は使わず、係数比較・階乗部分環の mod p 降下・明示切断表示を使う。
R/ϖ 係数との比較、prismatic envelope の Frobenius 引戻しとの同定はなお未完了。
今回の無限根環上の実分冪包だけで依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4421 jobs）。
新規 22 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3171 宣言の推移的公理依存は標準 3 公理のみ。
実係数商同型・モニック入力の実 mod p 正則性・完全 prism の実構造と普遍性・
切断表示同型・自由性の公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.34：係数同型での実構造の移送と A/(p) 無限根環上の自由・忠実平坦性

新規 `Andre/PrincipalDPRingEquiv.lean` は、任意の可換係数環同型 e:A≃B に対し、
自由一元分冪代数の実環同型と一次関係商の実環同型を構成する。
係数と全標準生成元の値を保つ。入力像の等式 e(y)=z を明示した版も公開する。
係数環の標数・正則性・非零性は要求せず、逆合成は任意係数の標準分冪基底で検証する。

新規 `Andre/PrincipalDPTransport.lean` は、その同型が正次数生成元イデアルを保つことを証明し、
元の実分冪構造を移す。入力元の分冪が標準生成元に一致する公式と、
任意の分冪標的への係数代数射の一意存在も移送する。
この一般補題では元の構造と値を明示引数にするが、次の実適用では両方を構成済み結果から供給する。

新規 `Andre/PowerRootCoefficientPDEnvelope.lean` は、E1.33 の実係数比較をこの移送に適用する。
係数環 `R=A/(p)`、`N=PowerRootPolynomial R p hp` とし、
`z=powerRootCoefficientPDInput p f` は係数を mod p に写した f の Y₀ 評価と定義する。
`PowerRootCoefficientPDEnvelope p f = PrincipalDPPresentation N z` が共通の実台環である。
名前付き入力は、型照合で評価の内部を展開し続けないため irreducible とする。
完全 prism W 上のモニック f について、正次数イデアルの実分冪構造
`powerRootCoefficientDividedPowers`、標準値の公式、
`existsUnique_powerRootCoefficientPDMorphism` による実 pd 普遍性を得た。
追加の構造・標準値・入力の正則性を前提として残さない。

同じ台環について `powerRootCoefficientPDEnvelope_truncatedEquiv` は、既存の
`principalDPQuotientAlgebra` が指定する `N/(z^p)` 上の可算切断表示への代数同型を与える。
また既存の無限根モニック冪商の基底計算により、元の R 上の自由性と忠実平坦性を証明する。
主要公開型（namespace `SerrePositivity.BhattScholze.Andre`）：

```lean
theorem powerRootCoefficientPDEnvelope_free
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (f : Polynomial A) (hf : f.Monic) :
    Module.Free (A ⧸ Ideal.span {(p : A)}) (PowerRootCoefficientPDEnvelope p f)

theorem powerRootCoefficientPDEnvelope_faithfullyFlat
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)}) (PowerRootCoefficientPDEnvelope p f)
```

自由性・忠実平坦性自体は完全 prism や δ 構造を要求しない。
忠実平坦性の正次数は元の f に対して述べ、係数商が零環の場合は自明性で扱う。
非零係数商ではモニック多項式の次数保存により、既存の正次数条件を内部で供給する。
実 pd 構造・普遍性には `(W : OrientedPrism p A)` と `W.deltaStructure.IsPerfect` を明示する。
`existsUnique_powerRootCoefficientPDMorphism` は任意の N 代数 T と分冪イデアル `(I,Ht)`、
z の像の I への所属に対し、上記の同じ台環から T への N 代数分冪射の一意存在を主張する。
標的のねじれ・正則性・δ 構造・完備性には条件を置かない。

BS Rem 7.15(1)（著者版 p.62）の通常自由性と実 pd 包の構造を同じ係数環・台環へそろえた。
原典の Prop 7.11 は使わず、階乗部分環の mod p 降下・係数環同型での移送・明示基底を使う。
原典の係数 R/ϖ への比較、prismatic envelope の Frobenius 引戻しとの同定はなお未完了。
今回の A/(p) 係数での結果だけで依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4424 jobs）。
新規 30 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3243 宣言の推移的公理依存は標準 3 公理のみ。
一般係数同型・構造移送・実係数商上の構造と普遍性・自由性・忠実平坦性・
切断表示の公開型 7 本を `#print` で確認した（終了コード 0）。

### E1.35：正次数商の自由性と正則係数元による実分冪構造の降下

新規 `Andre/PrincipalDPPositiveQuotient.lean` は、任意の可換環 A と y に対して
一次関係商 D=`PrincipalDPPresentation A y` の正次数イデアル J による商を、
元の入力商 A/(y) と A 代数同型にする。
零イデアルの分冪構造への標準評価を augmentation とし、係数からの逆射を構成する。
逆合成は商の係数代表元と全標準分冪生成元で確認する。
標数・正則性・非零性も、D 自身の分冪構造も要求しない。

```lean
def principalDPPositiveQuotientEquiv
    {A : Type u} [CommRing A] (y : A) :
    (PrincipalDPPresentation A y ⧸ principalDPPositiveIdeal y) ≃ₐ[A]
      (A ⧸ Ideal.span {y})
```

新規 `Andre/DividedPowerRegularQuotient.lean` は、分冪イデアル J を持つ D の元 a が
D/J で正則なら、実商 D/(a) 内の J の像に実分冪構造が降りることを証明する。
ab が J に属せば b も属すため、γₙ(ab)=aⁿγₙ(b) は正次数 n で (a) に属する。
これにより (a) と J の交わりの分冪安定性を得て、既存の商分冪構成を適用する。
商での分冪値の公式と標準商射の分冪保存も公開した。
D 自身での a の正則性は不要であり、D/J での正則性を正確な仮定にしている。

```lean
def dividedPowersQuotientOfRegular
    {D : Type u} [CommRing D] {J : Ideal D} (H : DividedPowers J) (a : D)
    (ha : IsSMulRegular (D ⧸ J) (Ideal.Quotient.mk J a)) :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {a})))
```

新規 `Andre/PowerRootCoefficientPDRegularReduction.lean` は、E1.34 の同じ実台環 D と
正次数イデアル J にこの降下を適用する。
通常のモニック入力商の既存基底と上記の同型により、D/J は R=A/(p) 上自由。
従って R 内で正則な a は D/J でも正則となる。
平坦性インスタンスはこの同じ自由性から型を明示して供給し、追加仮定は置かない。
完全 prism W とモニック f に対する `powerRootCoefficientPDRegularReduction` は
D 内の係数像 a による実商上の分冪構造。
`powerRootCoefficientPDRegularReduction_base_apply` は入力元の n 次分冪が
標準生成元の商像に一致することを、同 `_isDPMorphism` は標準商射の分冪保存を主張する。

ここで R=A/(p)、N=`PowerRootPolynomial R p hp`、z=`powerRootCoefficientPDInput p f`、
D=`PowerRootCoefficientPDEnvelope p f`、J=`principalDPPositiveIdeal z` とすると、主要公開型は

```lean
def powerRootCoefficientPDRegularReduction
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D a})))
```

BS Rem 7.15(1)（著者版 p.62）の R/ϖ 係数への比較を進めるための降下である。
原典の Prop 7.11 は使わず、通常入力商の基底と分冪イデアルの交わりの計算を使う。
a と原典の ϖ の対応、その係数商・台環・普遍性の比較、および prismatic envelope の
Frobenius 引戻しとの同定はなお未完了。正則係数元を明示した今回の降下だけで
依頼全体の完成とは数えない。
集約対象の `set -o pipefail; lake build
SerrePositivity.BhattScholze.Andre.MonicRootedExtension` は終了コード 0（4427 jobs）。
新規 20 公開宣言の `assert_no_sorry` を追加した専用監査は終了コード 0。
生成宣言を含む 3301 宣言の推移的公理依存は標準 3 公理のみ。
正次数商の同型・一般分冪降下・無限根正次数商の自由性と正則性・実還元構造・
標準値・商射の分冪保存の公開型 7 本を `#print` で確認した（終了コード 0）。

### E1.36：逆 Frobenius による ϖ の選択と実係数商の同型

新規 `Andre/PerfectPrismVarpi.lean` は完全 oriented prism W=(A,(d)) に対し、
x=φ⁻¹(d) と ϖ=x mod d を具体的に選ぶ。
逆 Frobenius の δ 射性から δ(x) は単元であり、d=x^p+pδ(x) を商へ移すと
ϖ^p=p·(−δ(x) mod d)。従って (ϖ^p)=(p) となる。
これらは R=A/(d) の p 正則性・非零性を仮定せず成立する。
一般 δ 環の distinguished 元について (φ(x),x)=(p,x) を証明し、
ここでは (d,x)=(p,x) を得る。

主要公開宣言は、p:ℕ、[Fact p.Prime]、[CommRing A]、
W:`OrientedPrism p A`、hW:`W.deltaStructure.IsPerfect` に対する

```lean
theorem perfectPrismVarpi_span_pow :
    Ideal.span {perfectPrismVarpi W hW ^ p} =
      Ideal.span {(p : A ⧸ W.ideal)}

def perfectPrismVarpiQuotientEquiv :
    ((A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}) ≃+*
      ((A ⧸ Ideal.span {(p : A)}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)})
          (perfectPrismVarpiLift W hW)})
```

同 `_mk` は A から来る二重商の代表元を保つことを主張する。
主イデアル二重商の一般同型 `principalDoubleQuotEquiv` とその代表元公式も公開した。
単なる型の書換えで同型を定義せず、標準二重商同型と等しいイデアル間の商同型を合成し、
係数上で計算できる射を指定する。

BS Rem 7.15（著者版 p.62）の R/ϖ 係数の具体化である。
原典の ϖ の選択を指定 prism の生成元の逆 Frobenius で明示したものであり、
今回だけでは prismatic envelope の Frobenius 引戻しを pd 包と同定していない。
x mod p の正則性を R の p 正則性から導く工程、E1.35 の分冪降下との接続、
その商の pd 普遍性・切断表示の係数比較、prismatic envelope との同定は未完了。
存在定理は承認済み hdeg 付きで既に証明済みだが、依頼全体の完成とは数えない。

対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4428 jobs）。
新規 12 公開宣言の `assert_no_sorry` を含む専用監査は終了コード 0。
生成宣言を含む 3328 宣言の推移的公理依存は標準 3 公理のみ。
主イデアル等式・二元イデアル等式・係数商同型・代表元公式の公開型 4 本を
`#print` で確認した（終了コード 0）。

### E1.37：p 正則な prism 商からの ϖ 持上げの正則性と実分冪降下

新規 `Andre/PerfectPrismVarpiRegular.lean` は、完全 oriented prism W=(A,(d)) に対し
R=A/(d) が p 正則なら、E1.36 の x=φ⁻¹(d) の mod p 像も正則であることを証明する。
まず任意の可換環で a が正則、b が A/(a) で正則なら a は A/(b) で正則とする
`principal_regular_swap` を証明した。ac=be を mod a で調べると e=at、
a を消去して c=bt を得る。完備性・局所性・b 自身の正則性は不要。
これを a=d、b=p に適用し、mod p の x^p=d と正の冪の正則性判定を使う。

```lean
theorem perfectPrismVarpiLift_modPrime_regular
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))
```

A は任意の可換環、p は素数とする。
この hpR を明示した上で、モニック f に対する E1.35 の実分冪降下に
x mod p を供給する `perfectPrismVarpiPowerRootDividedPowers` を構成した。
R₀=A/(p)、N=`PowerRootPolynomial R₀ p hp`、z=`powerRootCoefficientPDInput p f`、
D=`PowerRootCoefficientPDEnvelope p f`、J=`principalDPPositiveIdeal z`、
a=`Ideal.Quotient.mk (Ideal.span {(p : A)}) x` とすると、公開型は

```lean
def perfectPrismVarpiPowerRootDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R₀ D a})))
```

同 `_base_apply` は入力元の全 n 次分冪が標準分冪生成元の実商像であること、
同 `_isDPMorphism` は還元前の実分冪構造からの標準商射が分冪を保つことを主張する。
BS Rem 7.15（著者版 p.62）の p ねじれなしの場合に沿う接続であり、
公開済みの一般の存在定理に hpR を加えたり、一般基底をこの場合に置き換えたりしない。
今回の接続は条件付きの中間結果である。
商台環の係数変更後の pd 普遍性・切断表示との同型、原典の prismatic envelope の
Frobenius 引戻しとの同定、および一般基底に対する原典通りの比較は未完了。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4429 jobs）。
新規 6 公開宣言を `assert_no_sorry` に追加した専用監査は終了コード 0。
生成宣言を含む 3347 宣言の推移的公理依存は標準 3 公理のみ。
順序交換・持上げの正則性・実分冪構造・標準値・商射の分冪保存の公開型 5 本を
`#print` で確認した（終了コード 0）。

### E1.38：ϖ 持上げで還元した実 pd 包の存在・一意性の普遍性

新規 `Andre/PrincipalDPQuotientUniversal.lean` は、一次関係商
D=`PrincipalDPPresentation A y` の任意のイデアル K による商 Q を扱う。
正次数イデアル J の商像に実分冪構造 Hq があり、
入力元の n 次分冪が標準生成元の商像になるなら、K を標準評価で殺す任意の分冪標的へ
A 代数射として一意な分冪射が存在する。
標的の正則性・ねじれなし・標数・完備性は一切要求しない。
標準評価の実商への降下、代表元・標準生成元での評価公式、分冪保存も公開した。
分冪保存は正次数生成元で分冪合成則を比較して証明し、一意性は元の一次関係商の
生成元による外延性へ帰着する。商の構造と標準値は明示引数とする一般補題である。

```lean
theorem existsUnique_principalDPQuotientMorphism
    {A : Type u} [CommRing A] (y : A)
    (K : Ideal (PrincipalDPPresentation A y))
    {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
    (Ht : DividedPowers I) (hyB : algebraMap A B y ∈ I)
    (hK : ∀ t ∈ K, principalDPEval Ht y hyB t = 0)
    (Hq : DividedPowers ((principalDPPositiveIdeal y).map (Ideal.Quotient.mk K)))
    (hγ : ∀ n, Hq.dpow n
      (Ideal.Quotient.mk K (algebraMap A (PrincipalDPPresentation A y) y)) =
        Ideal.Quotient.mk K (principalDPGenerator y n)) :
    ∃! F : (PrincipalDPPresentation A y ⧸ K) →ₐ[A] B,
      Hq.IsDPMorphism Ht F.toRingHom
```

新規 `Andre/PerfectPrismVarpiPDUniversal.lean` は E1.37 の実分冪構造と標準値を
この一般補題に供給し、補助的な構造仮定なしに次の実普遍性を証明した。
A は可換環、p は素数、W=(A,(d)) は完全 oriented prism、
hpR は R=A/(d) の p 正則性、f は A 上モニックとする。
R₀=A/(p)、N=`PowerRootPolynomial R₀ p hp`、z=`powerRootCoefficientPDInput p f`、
D=`PowerRootCoefficientPDEnvelope p f`、x=`perfectPrismVarpiLift W hW`、
a=`Ideal.Quotient.mk (Ideal.span {(p : A)}) x` と置く。

```lean
theorem existsUnique_perfectPrismVarpiPDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra N B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap N B z ∈ I)
    (haB : algebraMap N B (algebraMap R₀ N a) = 0) :
    ∃! F : (D ⧸ Ideal.span {algebraMap R₀ D a}) →ₐ[N] B,
      (perfectPrismVarpiPowerRootDividedPowers W hW hpR f hf).IsDPMorphism Ht F.toRingHom
```

haB は係数変更後の標的を表す通常の零化条件である。
この条件と代数射の係数保持から標準評価が係数主イデアル全体を殺すことを導いた。
正次数仮定は不要。hpR はこの原典比較用の中間結果にだけ要求し、
既存の任意基底の根付き perfectoid 拡大定理の型には加えない。
BS Rem 7.15(1)（著者版 p.62）の係数還元後の pd 普遍性であり、
Prop 7.11 による経路は用いない。
原典の R/ϖ 上の無限根環への台環同型と切断表示の係数比較、
prismatic envelope の Frobenius 引戻しとの同定、一般基底への原典通りの比較は未完了。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4431 jobs）。
新規 6 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3376 宣言の推移的公理依存は標準 3 公理のみ。
商の標準評価・分冪保存・一般実普遍性・ϖ 還元の実普遍性の公開型 4 本を
`#print` で確認した（終了コード 0）。

### E1.39：ϖ 係数還元した無限根入力環と原典の R/ϖ 係数

新規 `Andre/PowerRootCoefficientQuotient.lean` は任意の可換環 A、正の p、任意の c:A に
対して、無限根環 P=`PowerRootPolynomial A p hp` の c の係数像による実商を
`PowerRootPolynomial (A/(c)) p hp` と環同型にする。
係数商射から誘導される環射の全射性と、その核が c の係数像の主イデアルであることを
係数ごとに証明し、第一同型定理を使う。
c の正則性・係数環の標数・非零性は仮定しない。
単項式、係数、全根変数、通常多項式の評価に対する計算公式も公開した。
既存の mod p 専用ファイルは変更せず、一般の係数主イデアルの計算を新規追加した。

```lean
def powerRootCoefficientQuotientEquiv
    (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (c : A) :
    (PowerRootPolynomial A p hp ⧸
      Ideal.span {algebraMap A (PowerRootPolynomial A p hp) c}) ≃+*
        PowerRootPolynomial (A ⧸ Ideal.span {c}) p hp
```

新規 `Andre/PerfectPrismVarpiRootInput.lean` は完全 oriented prism W=(A,(d)) に対して
この同型を R₀=A/(p)、x=φ⁻¹(d)、a=x mod p に適用し、E1.36 の係数商同型の逆を
モノイド環へ持ち上げた同型と合成する。
ϖ=`perfectPrismVarpi W hW`、N=`PowerRootPolynomial R₀ p hp` とすると主要公開型は

```lean
def perfectPrismVarpiRootInputEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    (N ⧸ Ideal.span {algebraMap R₀ N a}) ≃+*
      PowerRootPolynomial ((A ⧸ W.ideal) ⧸ Ideal.span {ϖ}) p hp
```

ここで [Fact p.Prime] と [CommRing A] を仮定するが、R=A/(d) の p 正則性は不要。
`perfectPrismVarpiRootInputEquiv_single` と同 `_coeff` は A から来る係数を保ち、
同 `_variable` は全根変数を同じ番号の変数に送る。
同 `_input` は任意の f:Polynomial A に対し、名前付き入力
`powerRootCoefficientPDInput p f` の係数還元像が、
R/ϖ 上へ係数を写した同じ多項式の根変数での評価であることを主張する。
この等式にモニック性は不要。
`perfectPrismVarpiRootInput_monic_regular` はモニック f なら、実入力商 N/(a) 内の
その入力像が正則であることを原典の係数環上のモニック入力の正則性から移す。
f の正次数や prism 商の p 正則性は不要である。

BS Rem 7.15（著者版 p.62）の R/ϖ[Y^(1/p^∞)] の台環と入力を具体化した。
原典の係数環との比較を通常の有限台モノイド環と実主イデアル商で計算する経路であり、
Prop 7.11 は使わない。
E1.38 の還元済み pd 包自体とこの入力上の標準表示との同型、切断表示の係数比較、
prismatic envelope の Frobenius 引戻しとの同定は未完了。
入力台環の比較だけを pd 包全体・prismatic envelope の同定とは数えない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4433 jobs）。
新規 16 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3442 宣言の推移的公理依存は標準 3 公理のみ。
一般係数商同型・ϖ 入力環同型・入力元比較・モニック入力の正則性の公開型 4 本を
`#print` で確認した（終了コード 0）。

### E1.40：pd 表示環自体の係数商比較と原典の係数環上の実普遍性

新規 `Andre/RankOneDPCoefficientQuotient.lean` は、自由一元分冪代数の係数変更射が
標準分冪基底の各座標を係数環射で送ることを証明した。
全射な係数環射に対する全射性を、標準基底展開と像部分環の有限和で証明する。
係数主イデアル商射の核は各基底座標の可除性から係数元の主イデアルに一致する。
第一同型定理により、Γ_A(A)/(c) と Γ_(A/(c))(A/(c)) の具体的な環同型を得た。
標数・正則性・非零性を要求しない。

新規 `Andre/PrincipalDPCoefficientQuotient.lean` は、自由分冪環内の係数主イデアルと
一次関係 γ₁=y のイデアルによる二重商の順序を交換し、さらにその係数商同型の下で
一次関係の像を計算する。これにより実表示環自体について

```lean
def principalDPCoefficientQuotientEquiv
    {A : Type u} [CommRing A] (c y : A) :
    ((PrincipalDPPresentation A y) ⧸
      Ideal.span {algebraMap A (PrincipalDPPresentation A y) c}) ≃+*
        PrincipalDPPresentation (A ⧸ Ideal.span {c})
          (Ideal.Quotient.mk (Ideal.span {c}) y)
```

を構成した。自由分冪代表元、標準係数、全標準分冪生成元での公式を公開した。
係数元の表示の違いと入力を保つ係数環同型をまとめる一般同型
`principalDPReducedCoefficientEquiv` とその係数・生成元公式も公開する。
具体的な無限根係数をすべて展開するとカーネル検査が時間上限に達したため、
計算規則をこの一般補題で証明し、具体例では検証済みの式を適用する。
心拍上限は増やさず、一般計算と具体的な係数環を分離して検証した。

新規 `Andre/PerfectPrismVarpiPDComparison.lean` はこれを E1.39 の入力環同型に適用した。
W=(A,(d)) を完全 oriented prism、x=φ⁻¹(d)、ϖ=x mod d、R₀=A/(p)、a=x mod p とする。
N=`PowerRootPolynomial R₀ p hp`、z=`powerRootCoefficientPDInput p f`、
D=`PowerRootCoefficientPDEnvelope p f`、Rv=R/ϖ、Nv=`PowerRootPolynomial Rv p hp`、
barr:A→Rv を二重商射、zv=`powerRootPolynomialBaseMap Rv p hp (f.map barr)` と置く。

```lean
def perfectPrismVarpiPDEnvelopeEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A) :
    (D ⧸ Ideal.span {algebraMap R₀ D a}) ≃+* PrincipalDPPresentation Nv zv
```

この同型自体に f のモニック性・prism 商の p 正則性は不要。
係数・全標準分冪生成元・入力元を保つこと、正次数イデアルの実像が
原典の入力 zv の正次数イデアルに一致することも証明した。

新規 `Andre/PerfectPrismVarpiNativePDEnvelope.lean` は、モニック f と
hpR:`IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)` の下で、
E1.37 の実分冪構造をこの同型で移し、原典の Nv 上の標準表示そのものに
`perfectPrismVarpiNativeDividedPowers` を構成する。
同 `_base_apply` は入力元の n 次分冪が標準生成元に一致することを主張する。
実構造の存在と標準値を一般の pd 普遍性に供給し、

```lean
theorem existsUnique_perfectPrismVarpiNativePDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
    ∃! F : PrincipalDPPresentation Nv zv →ₐ[Nv] B,
      (perfectPrismVarpiNativeDividedPowers W hW f hpR hf).IsDPMorphism Ht F.toRingHom
```

を証明した。A は可換環、p は素数とする。
標的 B のねじれなし・完備性・δ 構造は仮定しない。
この結論は表示環だけでなく、原典の係数環上の同じ台環の実分冪構造と普遍性を持つ。
BS Rem 7.15(1)（著者版 p.62）の通常 pd 包の計算であり、Prop 7.11 は用いない。
今回の構造・普遍性は hpR 付きの中間結果である。
同じ台環の切断表示と忠実平坦性の原典係数での接続、
prismatic envelope の Frobenius 引戻しとの同定、および一般基底への比較は未完了。
公開済みの一般の存在定理の前提は変更していない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4437 jobs）。
新規 21 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3587 宣言の推移的公理依存は標準 3 公理のみ。
自由分冪・一次関係表示の係数商同型、ϖ 還元表示の同型とイデアル対応、
原典係数上の実分冪構造・pd 普遍性の公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.41：原典係数上の同じ実 pd 台環の切断表示・自由性・忠実平坦性

新規 `Andre/PerfectPrismVarpiNativePDFlat.lean` は、E1.40 で実分冪構造と普遍性を
与えた標準台環そのものに、既存の可算切断表示とモニック冪商の計算を接続した。
W=(A,(d)) は完全 oriented prism、x=φ⁻¹(d)、ϖ=x mod d、Rv=(A/(d))/(ϖ)、
Nv=`PowerRootPolynomial Rv p hp`、barr:A→Rv は標準二重商射、
zv=`powerRootPolynomialBaseMap Rv p hp (f.map barr)`、
Dv=`PrincipalDPPresentation Nv zv` とする。
Rv と (A/p)/(x mod p) の具体的環同型で p=0 を証明し、Nv にも移す。

```lean
def perfectPrismVarpiNativePDEnvelope_truncatedEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) zv
    Dv ≃ₐ[Nv ⧸ Ideal.span {zv ^ p}] PrincipalDPTruncatedPresentation p zv
```

右辺は実際の可算変数多項式商 `(Nv/(zv^p))[g₁,g₂,…]/(gᵢ^p)`。
係数作用は既存の `principalDPQuotientAlgebra` を固定しており、単なる環同型ではなく
入力の p 乗商からの標準係数射を保つ代数同型である。
`perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient` はこの同じ係数商上の自由性、
`perfectPrismVarpiRootInput_free` は Nv 自身の Rv 上の自由性、
`perfectPrismVarpiRootPowerQuotient_free` はモニック f に対する Nv/(zv^p) の
Rv 上の自由性、`perfectPrismVarpiNativePDEnvelope_free` は Dv の Rv 上の自由性を述べる。
これらの加群の結果は prism 商の p 正則性を要求しない。
正次数モニック f に対しては

```lean
theorem perfectPrismVarpiNativePDEnvelope_faithfullyFlat
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat Rv Dv
```

を証明した。非零 Rv ではモニック多項式の次数保存、零 Rv では任意加群の自明性を使い、
係数環の非零性を追加仮定にしない。

`perfectPrismVarpiNativePDEnvelope_truncated_dpow` は、E1.40 の実分冪構造の
入力元における p^(i+1) 次分冪が切断表示の添字 i の変数に写ることを証明する。
この分冪構造を含む公式には従前通り hpR（A/(d) の p 正則性）と hf を明示する。
表示と加群の結果には hpR を要求しないことと区別する。
BS Rem 7.15(1)（著者版 p.62）の P/(f^p) 上の自由な切断表示と R/ϖ 上の
忠実平坦性の通常代数計算を、構成済みの同じ実 pd 台環に接続した。
Prop 7.11 を使わず、具体的基底と係数射を保持する既存表示の経路である。
prismatic envelope の Frobenius 引戻しとの同定、その比較を用いた T/ϖ の
忠実平坦性・T の p ねじれなし、および一般基底への原典通りの比較は未完了。
公開済みの根付き perfectoid 拡大の一般存在定理をこの条件付き比較で置き換えない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4438 jobs）。
新規 9 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3618 宣言の推移的公理依存は標準 3 公理のみ。
切断代数同型・入力 p 乗商上の自由性・忠実平坦性・無限根環と冪商の自由性・
実分冪値の切断変数への対応の公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.42：無限根入力の δ 完全性と raw 除算包の Frobenius 係数変更

原典の著者版 p.62 をページ画像でも再確認した。
Rem 7.15 の T は `overline(Δ)_S` と記されている。したがって、ここで残る比較では
prism 台環 Δ とその Hodge–Tate 商 T を区別し、Frobenius による係数作用の向きを
追跡する必要がある。Cor 2.39（p.25）は φ(f)/p の δ 包と pd 包の比較であり、
Frobenius を省略した f/p の包との同定は主張していない（原典 Warning 2.41 も参照）。
今回の raw 係数変更同型だけを、Rem 7.15 の完備化済みの剰余比較と数えない。

新規 `Andre/PowerRootPolynomialPerfectDelta.lean` は、無限根指数の p 倍の単射性・
全射性を証明し、同じ加法射を `powerRootExponentPrimeScaleEquiv` として束ねた。
全射性では有理数 q/p の分母条件を一段先で検証する。
係数 Frobenius 同型と指数 p 倍の同型から無限根環の標準 Frobenius の環同型を構成し、
既存の標準 δ 構造の完全性を証明した。

```lean
theorem powerRootPolynomialDelta_isPerfect
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (D : DeltaStructure p A) (hD : D.IsPerfect) :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsPerfect
```

p 正則性は hD から供給し、係数環の非零性や追加の正則性を仮定しない。
台環は従前と同じ未完備の `PowerRootPolynomial A p hp`。

新規 `Andre/DeltaDivisionCoefficientAut.lean` は任意の δ 自己同型 e:A≃A に対し、
raw δ 包 A{a/d} と A{e(a)/e(d)} の具体的な環同型を構成した。
順・逆の係数射と同じ添字の除算変数を指定して既存の δ 除算の普遍性を使い、
逆合成は係数と初期変数での外延性により確認する。

```lean
def deltaDivisionCoefficientAutEquiv
    {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
    (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
    (d : A) (a : σ → A) :
    DeltaAdjoinDivision D d a ≃+*
      DeltaAdjoinDivision D (e d) (fun s => e (a s))
```

同 `_coeff`、`_variable`、`_isDeltaHom` は e 半線形の係数公式、
全初期変数の保存、実 δ 射であることを述べる。
d の正則性や係数環の完全性はこの一般同型には要求しない。

これを無限根 δ 環の Frobenius 自己同型へ適用し、
`powerRootPolynomialDivisionFrobeniusEquiv` を構成した。
P=`PowerRootPolynomial A p hp`、E=`powerRootPolynomialDelta p hD.p_mul_injective D`
とすると公開型は

```lean
def powerRootPolynomialDivisionFrobeniusEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) :
    DeltaAdjoinDivision E d a ≃+*
      DeltaAdjoinDivision E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s))
```

同 `_coeff`、`_variable`、`_isDeltaHom` も公開した。
任意の族を扱うため、一元モニック入力を定数 Unit 族として適用できる。
BS Rem 7.15（著者版 p.62）の原典比較のための raw δ 環の係数変更であり、
Cor 2.39（p.25）や Prop 7.11 を引用として追加していない。
完備化、Hodge–Tate 商・ϖ 商への移行、係数 Frobenius の剰余環での作用、
その pd 包との比較、T/ϖ の忠実平坦性と T の p 正則性は引き続き未完了。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4440 jobs）。
新規 18 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3685 宣言の推移的公理依存は標準 3 公理のみ。
無限根 δ 完全性、一般 raw 同型と係数公式、無限根 raw Frobenius 同型と
その δ 互換性の公開型 5 本を `#print` で確認した（終了コード 0）。

### E1.43：raw 二重剰余の Frobenius 比較と R/ϖ → R/p の係数作用

新規 `Andre/DeltaDivisionFrobeniusResidue.lean` は、E1.42 の raw δ 自己同型比較を
任意の二元係数イデアルの商へ降ろす。
完全 δ 環 D 上の distinguished 元 d に対し、x=φ⁻¹(d)、
L=`DeltaAdjoinDivision D d a`、M=`DeltaAdjoinDivision D (φ d) (φ ∘ a)`、
jL、jM をそれぞれの係数射とすると、
(d,x) の像は (φ(d),d)=(p,d) である。
二重主イデアル商の順序も明示して次の通常環同型を構成した。

```lean
def deltaDivisionFrobeniusDoubleResidueEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (hD : D.IsPerfect) (hd : D.IsDistinguished d) :
    ((L ⧸ Ideal.span {jL d}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {jL d}) (jL x)}) ≃+*
        ((M ⧸ Ideal.span {jM d}) ⧸
          Ideal.span {(p : M ⧸ Ideal.span {jM d})})
```

同 `_coeff` は二重商の係数 b を φ(b) に送ることを主張する。
二元商の同型 `deltaDivisionFrobeniusResidueEquiv` と係数・初期変数の公式も公開した。
δ 閉包商を d で割った後に δ 構造が残るとは主張せず、通常環同型として降ろしている。

新規 `Andre/PerfectPrismVarpiFrobeniusQuotient.lean` は完全 prism W=(A,(d)) に対し

```lean
def perfectPrismVarpiFrobeniusQuotientEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) :
    ((A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}) ≃+*
      ((A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)})
```

を構成した。
同 `_mk` は A 由来の代表元 b に係数 Frobenius を適用する公式、
同 `_mk_pow` はこの像が R/p で b の p 乗を取ることと一致する公式。
prism 商の p 正則性・非零性は仮定しない。
Frobenius の向きは R/ϖ から R/p であり、単なる抽象環同型ではなく係数作用を記録する。
二重商の計算では係数射の p の像と商環内の自然数 p を明示的な等しいイデアル間の
商同型で結んでおり、標準係数射を取り替えない。

新規 `Andre/PowerRootPrismFrobeniusResidue.lean` は上記の raw 比較を
P=`PowerRootPolynomial A p hp`、
E=`powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure` に適用する。
prism 生成元の係数像 dP は E に関して distinguished であることを係数 δ 射から供給し、
E の Frobenius による dP の逆像が、選択済みの
xP=`algebraMap A P (perfectPrismVarpiLift W hW)` と一致することを証明する。
任意の入力族 a:σ→P に対する `powerRootPrismFrobeniusDoubleResidueEquiv` は、
左辺の二重商に xP を使い、右辺を Frobenius 側の dP,p 二重商にする実環同型。
同 `_coeff` で P 全体の係数代表元 b に E の標準 Frobenius を適用することを述べる。
モニック性や prism 商の p 正則性、補助的な distinguished 性は仮定しない。

BS Rem 7.15（著者版 p.62）の二つの剰余操作を係数射とともに具体化した。
ここでの同型は未完備 raw 包の比較であり、
完備化後の Hodge–Tate 商 T=overline(Δ)_S の比較とは区別する。
原典の φ_A による係数変更と、P 全体の Frobenius による指数 p 倍を含む作用の比較、
完備化後の剰余との可換性、および pd 包との同定は引き続き未完了。
原典の Cor 2.39・Prop 7.11 を新たな引用に追加しない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4443 jobs）。
新規 17 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3808 宣言の推移的公理依存は標準 3 公理のみ。
一般 raw 二重剰余同型と係数公式、R/ϖ の Frobenius 同型と p 乗公式、
実無限根入力の raw 同型と係数公式の公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.44：係数 Frobenius と指数 Frobenius の分解と raw 射の合成

新規 `Andre/PowerRootFrobeniusFactors.lean` は完全 δ 係数環 D 上の
P=`PowerRootPolynomial A p hp` の Frobenius を二つの環同型に分けた。
C=`powerRootCoefficientFrobeniusEquiv p D hD` は係数だけを D.frobeniusLift で送り、
全根変数を固定する。V=`powerRootVariableFrobeniusEquiv p` は係数を固定し、
指数を p 倍して全根変数をその p 乗へ送る。
単項式・係数・根変数での公式と C,V の環射としての可換性を証明した。
E=`powerRootPolynomialDelta p hD.p_mul_injective D` とすると

```lean
theorem powerRootFrobeniusFactors_equiv
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
    (D : DeltaStructure p A) (hD : D.IsPerfect) :
    (powerRootCoefficientFrobeniusEquiv p D hD).trans
      (powerRootVariableFrobeniusEquiv (A := A) p) =
    (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusEquiv
      (powerRootPolynomialDelta_isPerfect p D hD)
```

を証明した。これは抽象的な分解の存在ではなく、既存の同じ δ 構造の Frobenius 同型との
等式である。p 正則性と全体 Frobenius との可換性から、C,V がともに実 δ 自己同型である
`powerRootCoefficientFrobeniusEquiv_isDeltaHom`、
`powerRootVariableFrobeniusEquiv_isDeltaHom` も証明した。
追加の係数環の非零性や正則性は要求せず、p 正則性は hD から供給する。

通常多項式 f について `powerRootCoefficientFrobeniusEquiv_baseMap` は
C(f(Y₀))=(f.map φ_A)(Y₀)、同 Variable 版は V(f(Y₀))=f(Y₀^p) を述べる。
モニック性は不要。これにより φ_A による係数変更と、P 全体の Frobenius に含まれる
指数 p 倍の作用を、同じ入力環と多項式評価の下で区別して追跡できる。

新規 `Andre/DeltaDivisionCoefficientAutComposition.lean` は、任意の係数 δ 自己同型
 e,f に対して、その raw 包の比較射が合成と両立することを証明した。
係数・初期変数の公式と δ 射の外延性だけを使い、分母の正則性は要求しない。

```lean
theorem deltaDivisionCoefficientAutMap_trans
    (D : DeltaStructure p A) (e f : A ≃+* A)
    (he : D.IsDeltaHom D e.toRingHom) (hf : D.IsDeltaHom D f.toRingHom)
    (d : A) (a : σ → A) :
    (deltaDivisionCoefficientAutMap D f hf (e d) (fun s => e (a s))).comp
      (deltaDivisionCoefficientAutMap D e he d a) =
    deltaDivisionCoefficientAutMap D (e.trans f) (hf.comp he) d a
```

新規 `Andre/PowerRootDivisionFrobeniusFactors.lean` は C,V の δ 互換性を実入力の
raw 比較へ供給し、`powerRootCoefficientDivisionFrobeniusEquiv` と
`powerRootVariableDivisionFrobeniusEquiv` を構成する。
`powerRootDivisionFrobeniusFactors_comp` は、前者の後に後者を適用した環射が
合成自己同型 C.trans V の raw 比較射と一致することを、上記の一般合成則から証明した。
任意の分母 d:P と任意族 a:σ→P を扱うため、モニック一元入力にも適用できる。

BS Rem 7.15（著者版 p.62）の原典の φ_A 作用を raw 入力の全体 Frobenius と結ぶ
具体的な代数計算である。原典にこの成分ごとのコード構成が述べられているわけではなく、
Prop 7.11・Hodge–Tate 比較を使わない構成のため、係数と指数を別々に検証した。
完備化後の商との可換性、T=overline(Δ)_S の剰余と pd 包との同定、
その比較による T/ϖ の忠実平坦性と T の p 正則性は引き続き未完了。
新しい引用や公開存在定理の追加仮定は加えていない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4446 jobs）。
新規 19 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3860 宣言の推移的公理依存は標準 3 公理のみ。
二成分の同型等式・係数成分の δ 互換性・両成分の多項式評価公式・
一般 raw 合成則・実入力の raw 合成則の公開型 6 本を `#print` で確認した（終了コード 0）。

### E1.45：raw 同型の実導来完備化への延長と完備化後の二元剰余

新規 `Andre/PDCompletionCoordinateEquiv.lean` は、既存 F3 の実際の
`PDCompletionH0`、`pdCompletionCommRing`、`pdCompletionUnit` を用い、
座標を保つ任意の環射 g:A→B、g(d)=d' の一意な延長を構成した。
標的自身の p,d' 導来完備性を、既存の環としての実 H⁰ 普遍性へ供給する。
環同型 e に対して順逆の延長を作り、標準単位との合成が一致することから
逆合成を一意性で証明した。

```lean
def pdCompletionCoordinateEquiv
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ)
    (e : A ≃+* B) (d : A) (d' : B) (hd : e d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    PDCompletionH0 A p d ≃+* PDCompletionH0 B p d'
```

同 `_unit` は全 b:A について標準像を e(b) の標準像へ送る公式。
任意の座標保存環射についての `existsUnique_pdCompletionCoordinateMap`、
選択した標準射 `pdCompletionCoordinateMap` とその単位との合成公式も公開した。
これらに素数性・正則性・Noether 性・古典的完備性を要求しない。
素数 p の δ 環射に対しては既存の実完備化 δ 普遍性で標準延長の δ 互換性を証明し、
同型版 `pdCompletionCoordinateEquiv_isDeltaHom` も公開する。
完備化の定義や標準係数射を別のモデルへ取り替えない。

新規 `Andre/DeltaDivisionCoefficientPDCompletion.lean` は、係数 δ 自己同型 e の
raw 比較が分母の係数像を保つことを、この座標付き完備化比較へ供給する。
L=A{a/d}、M=A{e(a)/e(d)}、jL,jM を元の係数射とすると

```lean
def deltaDivisionCoefficientPDCompletionEquiv
    (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
    (d : A) (a : σ → A) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (e d))
    PDCompletionH0 L p (jL d) ≃+* PDCompletionH0 M p (jM (e d))
```

を得る。同 `_unit`、`_coeff`、`_isDeltaHom` は raw 全元の標準像の保存、
元の係数 b の e(b) への半線形性、既存の完備化 δ 構造の保存を主張する。
d の正則性などの補助仮定は置かない。

新規 `Andre/DeltaDivisionFrobeniusCompletedResidue.lean` は、完全 δ 環 D の
Frobenius 自己同型にこれを適用する。
d は distinguished、x=φ⁻¹(d)、L=A{a/d}、M=A{φ(a)/φ(d)}、
HL=`PDCompletionH0 L p (jL d)`、HM=`PDCompletionH0 M p (jM (φ d))`、
uL,uM を標準完備化単位とすると

```lean
def deltaDivisionFrobeniusCompletedResidueEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (a : σ → A)
    (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    letI := pdCompletionCommRing M p (jM (φ d))
    (HL ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      (HM ⧸ Ideal.span {(p : HM), uM (jM d)})
```

を構成した。
像イデアルの計算 `deltaDivisionFrobeniusCompleted_pairIdeal` と、
係数 b を φ(b) の標準像の商へ送る同 `_coeff` も証明した。
実 H⁰ の環構造を明示し、Frobenius 側の raw 環と完備化座標を
同じ Frobenius 同型の順射で統一して供給している。

BS Rem 7.15（著者版 p.62）の raw 比較を実導来完備化へ持ち上げた段階である。
ここでの剰余比較は「実完備化 H⁰ を取った後の通常商」同士であり、
完備化と剰余の順序を交換したとの主張ではない。
未完備 pd 包の剰余との比較、実源の離散性・正則性による完備化後の剰余計算、
および原典の T=overline(Δ)_S との同定は引き続き未完了。
従って T/ϖ の忠実平坦性や T の p 正則性を今回の一般同型だけで結論しない。
原典の引用や公開存在定理の追加仮定は増やしていない。

対象・集約の `set -o pipefail; lake build` は終了コード 0
（集約 `SerrePositivity.BhattScholze.Andre.MonicRootedExtension`：4449 jobs）。
新規 14 公開宣言を `assert_no_sorry` に加えた専用監査は終了コード 0。
生成宣言を含む 3939 宣言の推移的公理依存は標準 3 公理のみ。
座標付き実完備化同型・単位公式・δ 互換性、raw 比較の実完備化同型、
完備化後の Frobenius 剰余同型と係数公式の公開型 6 本を `#print` で確認した（終了コード 0）。


### E1.46：実完備化 H⁰ の座標を殺す商から未完備剰余への比較（検証済み）

新規 `Andre/PDCompletionKilledCoordinates.lean` は、可換環 A、自然数 p、
d∈A、p,d を含む任意のイデアル I に対し、実導来 (p,d) 完備化の
H=`PDCompletionH0 A p d`、標準単位 u=`pdCompletionUnit A p d` を用いて
次の比較を構成する。

```lean
def pdCompletionQuotientEquivOfKilledCoordinates
    (p : ℕ) (d : A) (I : Ideal A)
    (hpI : (p : A) ∈ I) (hdI : d ∈ I) :
    letI := pdCompletionCommRing A p d
    (PDCompletionH0 A p d ⧸ I.map (pdCompletionUnit A p d)) ≃+* A ⧸ I
```

商 A/I と H/IH では両完備化座標が零なので導来完備である。
実 H⁰ の環としての一意延長性から逆射を構成し、両逆合成を検証した。
正則性・Noether 性・実源の離散性の仮定はこの通常商の比較には不要。
E1.45 で未完了としていた「完備化後の通常剰余を未完備剰余へ戻す」部分を、
この普遍性で解消した。高次ホモロジーの消滅をこの比較から主張しない。
標準射の一意延長・代表元公式・両逆合成を含む 12 公開宣言を追加した。

新規 `Andre/PDCompletionPairResidue.lean` の 3 公開宣言は、
c∈(p,d) なら、(p,c) に沿う実完備化 H⁰ を (p,u(d)) で割った環と
元の A/(p,d) が環同型であること、および u(b) の剰余が b の剰余へ
送られることを述べる。

新規 `Andre/DeltaDivisionFrobeniusCompletionToRaw.lean` は完全 δ 環 D、
distinguished 元 d、任意族 a にこれを適用する。
φ は D の Frobenius、x=φ⁻¹(d)、L=A{a/d}、M=A{φ(a)/φ(d)}、
jL,jM は標準係数射、HL は L の実 (p,jL(d)) 完備化 H⁰、uL は標準単位とする。

```lean
def deltaDivisionFrobeniusCompletionToRawEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (a : σ → A)
    (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    (HL ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      (M ⧸ Ideal.span {(p : M), jM d})
```

φ(d)=d^p+pδ(d)∈(p,d) により Frobenius 側の完備化座標が商で消える。
E1.45 の実完備化後の Frobenius 同型に二元商比較を合成した。
同 `_coeff` は係数 b が右辺の jM(φ(b)) の剰余へ送られると述べる。
座標のイデアル所属を含む 3 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の剰余計算への補助段階であり、
原典とは異なる実 H⁰ の環普遍性による証明である。
右辺の未完備 raw 剰余と具体的 pd 包の同定、および原典の
T=overline(Δ)_S との同定は引き続き未完了。
この工程だけで T/ϖ の忠実平坦性や T の p 正則性を結論しない。
公開存在定理には既承認の正次数仮定以外を追加していない。

3 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4452 jobs）。新規 18 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4011 宣言の推移的公理依存は標準 3 公理のみ。
標準延長、一般剰余同型とその単位公式、二元剰余同型、
Frobenius 完備化から raw への同型と係数公式の公開型 6 本を
`#print` で確認した（終了コード 0）。


### E1.47：Witt 解による raw 包の通常普遍性と分母の単元正規化（検証済み）

新規 `Andre/DeltaDivisionWittEvaluation.lean` は、源 A の p 正則性、
自由 δ 環 L₀=`RelativeFreeDeltaRing σ` の ghost 射の単射性を明示して、
任意の通常係数射 q:A→B と全 Witt 点 w_s から通常環射を構成する。
W_D(r)=`deltaWittGhostVector D r` と略記すると、公開する主な型は次である。

```lean
def deltaDivisionWittMap
    (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
    (q : A →+* B) (w : σ → WittVector p B) (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (W_D d) * w s = WittVector.map q (W_D (a s))) :
    DeltaAdjoinDivision D d a →+* B
```

逆 Witt 座標へ w_s の全係数を代入することで、初期除算関係の全 Witt 元を殺す。
既存の jet 消滅比較で全 δ 反復関係を殺し、通常商へ降ろす。
終域 B には δ 構造・p 正則性・完備性・標数の仮定を置かない。
`deltaDivisionRawWittPoint` は自由変数の全 Witt 元の raw 商像を定義する。
同 `_relation` はこの点が元の全 Witt 方程式を満たすと述べる。
`deltaDivisionRingHom_ext_of_wittPoint` は、通常環射二つが係数と全 raw Witt 点で
一致すれば等しいことを、可逆な Witt 座標変換から示す。
`existsUnique_deltaDivisionWittMap` は指定した係数射と全 Witt 点を保つ
通常環射の一意存在を述べる。評価公式を含め 15 公開宣言を追加した。

新規 `Andre/DistinguishedWittDenominator.lean` は distinguished d の分母を正規化する。
q:A→B、B は標数 p、q(d)=0 とし、A の p 正則性と A の ghost 射の単射性を明示する。
既存の具体的な係数ずらし v=`deltaPDivisionWittResidueSolution D q d` は
p v=`WittVector.map q (W_D (φ(d)))` を満たす。
v の定数係数は q(δd) であり、distinguished 性から単元である。
Mathlib の `WittVector.mkUnit` による再帰的逆元を使い、
値を v のまま保持する `distinguishedWittDenominatorUnit` を構成した。

```lean
def distinguishedWittDivisionSolutionEquiv
    (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
    (q : A →+* B) (d : A) (hd : D.IsDistinguished d)
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqd : q d = 0) (z : WittVector p B) :
    {w : WittVector p B // WittVector.map q (W_D (φ(d))) * w = z} ≃
      {w : WittVector p B // (p : WittVector p B) * w = z}
```

順方向を v 倍、逆方向を v⁻¹ 倍とし、両逆合成を証明した。
単元の定数係数・値・分母公式を含め 5 公開宣言を追加した。
BS Rem 7.15（著者版 p.62）の pd 包比較のための、原典とは異なる
具体的 Witt 座標による補助段階である。

次の工程は、これらの実通常環射を (p,d) 商へ降ろし、
A{φ(a)/φ(d)}/(p,d) と A{φ(a)/p}/(p,d) を比較すること。
今回その商環同型自体はまだ宣言・証明していない。
具体的 pd 包との同定、原典の T=overline(Δ)_S との同定も引き続き未完了。
公開存在定理に追加仮定・引用は増やしていない。

両対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4458 jobs）。新規 20 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4046 宣言の推移的公理依存は標準 3 公理のみ。
通常環射・Witt 点公式・外延性・raw 方程式・一意存在・単元の分母公式・
解の同値の公開型 7 本を `#check` で確認した（終了コード 0）。


### E1.48：Frobenius 分母と p 分母の raw 剰余同型、および実完備化との合成（検証済み）

新規 `Andre/DistinguishedWittDenominatorNaturality.lean` は、係数環 B に
正確な標数 p や非零性を要求せず、(p:B)=0 のみで分母正規化単元を構成する。
非零環では標数 p として前工程を適用し、零環では Witt 係数の一致を使う。
`distinguishedWittResidueUnit` の値は既存の具体的係数ずらしであり、
係数射を保つ通常環射で単元とその逆元の値が保たれる。
p v=qW(φ(d)) の公式を含め 7 公開宣言を追加した。

新規 `Andre/DeltaDivisionPairResidueWitt.lean` は通常二元剰余

```lean
abbrev DeltaDivisionPairResidue (D : DeltaStructure p A) (c : A) (b : σ → A) (d : A) :=
  DeltaAdjoinDivision D c b ⧸
    Ideal.span {(p : DeltaAdjoinDivision D c b), deltaAdjoinDivisionMap D c b d}
```

の標準係数射・全 Witt 点を明示する。
係数射 q:A→B が p,d を殺し、指定した Witt 点が W(c)w_s=W(b_s) を満たせば、
`deltaDivisionPairResidueLift` で実通常環射を作る。
その係数公式・Witt 点公式と、係数と全 Witt 点による通常環射の外延性を証明した。
剰余環の δ 構造・非零性・正則性は仮定しない。11 公開宣言を追加した。

新規 `Andre/DeltaDivisionFrobeniusPResidueEquiv.lean` はこの普遍性を二度使う。
源 A は p 正則、d は distinguished、A と自由 δ 環の ghost 射は単射とする。
分子族 b:σ→A は任意で、完全性・モニック性・有限性は仮定しない。

```lean
def deltaDivisionFrobeniusPResidueEquiv
    (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (hd : D.IsDistinguished d) (b : σ → A) :
    DeltaDivisionPairResidue D (D.frobeniusLift d) b d ≃+*
      DeltaDivisionPairResidue D (p : A) b d
```

順射は p 側の標準 Witt 点を正規化単元 v の逆元倍に、
逆射は Frobenius 側の標準 Witt 点を v 倍にする。
通常環射の普遍性で射を作り、単元の自然性と全 Witt 点の外延性で
両逆合成が恒等射と証明した。元の全 A 係数を保つことも公開する。
補助方程式・両射・係数と点公式・両逆合成を含め 16 公開宣言を追加した。

新規 `Andre/DeltaDivisionCompletionPResidue.lean` は完全 δ 環 D の場合に
E1.46 の実完備化から raw への比較を合成する。
x=φ⁻¹(d)、L=A{a/d}、jL は標準係数射、H=`PDCompletionH0 L p (jL d)`、
uL=`pdCompletionUnit L p (jL d)` とすると、公開型は

```lean
def deltaDivisionCompletionPResidueEquiv
    (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) (a : σ → A) :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      DeltaDivisionPairResidue D (p : A) (fun s => D.frobeniusLift (a s)) d
```

である。同 `_coeff` は uL(jL(r)) の剰余が右辺の φ(r) の係数像へ
送られることを述べる。元の実 H⁰ と標準単位は取り替えない。2 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の分母の問題を、原典とは異なる
具体的 Witt 解による通常環射で解消した段階である。
次は既存の raw p 除算包と主 pd 表示の実同型を二元商へ降ろし、
無限根入力の具体的 pd 包へ合成する。原典の T=overline(Δ)_S との同定と、
そこからの原典の経路による忠実平坦性・p 正則性の結論は引き続き未完了。
公開存在定理の追加仮定・引用は増やしていない。


4 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4462 jobs）。新規 36 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4155 宣言の推移的公理依存は標準 3 公理のみ。
正規化単元の分母公式・逆元の自然性、二元剰余への射と外延性、
分母変換同型と係数公式、実完備化剰余から raw p 剰余への同型と係数公式の
公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.49：raw p 剰余から主 pd 表示、および無限根モニック入力の実完備化への適用（検証済み）

新規 `Andre/PrincipalDPIdealQuotient.lean` は、係数主イデアル商の既存比較を
任意の係数イデアル K へ拡張した。自由分冪基底の各係数の K への所属を用いて
係数変更射の核を K の像イデアルと計算し、一次関係との二重商を交換する。

```lean
def principalDPIdealQuotientEquiv (K : Ideal A) (y : A) :
    (PrincipalDPPresentation A y ⧸ K.map (algebraMap A (PrincipalDPPresentation A y))) ≃+*
      PrincipalDPPresentation (A ⧸ K) (Ideal.Quotient.mk K y)
```

係数と全標準分冪生成元の公式を含め 8 公開宣言を追加した。
K の正則性・主性・係数環の標数は仮定しない。

新規 `Andre/DeltaPDivisionIdealPDComparison.lean` は、正則 raw φ(y)/p 包と
主 pd 表示の既存の実同型が係数を保つことを用いて、任意の係数イデアル商へ降ろす。
一元添字型 σ は Unique、A は p 局所かつ p 正則、y mod p は非零因子とし、
自由 δ 環の ghost 単射性と δ(p) を値に持つ単元 v を明示する。

```lean
def deltaPDivisionPairPDEquiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun r : A => (p : A) * r))
    (D : DeltaStructure p A) (y : A)
    (hgL : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (d : A) :
    DeltaDivisionPairResidue D (p : A) (fun _ : σ => D.frobeniusLift y) d ≃+*
      PrincipalDPPresentation (A ⧸ Ideal.span {(p : A), d})
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) y)
```

一般係数イデアル版、階乗生成元の標準分冪への像、二元剰余版の係数公式を含め
6 公開宣言を追加した。d の distinguished 性はこの段階には不要。

新規 `Andre/DeltaDivisionCompletionPrincipalPD.lean` は、D が完全、d が distinguished の場合に
E1.48 の実完備化から raw p 剰余への同型と上の実 pd 台環比較を合成する。
x=φ⁻¹(d)、L=A{y/d}、H=`PDCompletionH0 L p (jL d)`、uL は標準完備化単位とする。

```lean
def deltaDivisionCompletionPrincipalPDEquiv :
    letI := pdCompletionCommRing L p (jL d)
    (H ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      PrincipalDPPresentation (A ⧸ Ideal.span {(p : A), d})
        (Ideal.Quotient.mk (Ideal.span {(p : A), d}) y)
```

前提は上記の hA,hpA,hgL,v,hv,hy に加え D の完全性、A の ghost 単射性、
d の distinguished 性である。比較同型の存在を前提にしていない。
同 `_coeff` は uL(jL(r)) の剰余を φ(r) の剰余係数へ送る。2 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicCompletionPD.lean` は、完全 prism W 上の
無限根環 P とモニック f へ適用し、これらの補助仮定を全て内部で解消した。
E は P の既存 δ 構造、dP は W.generator の係数像、xP は選択済み
`perfectPrismVarpiLift W hW` の係数像、y=`powerRootMonicPDInput p f` とする。
一元族を固定した L=P{y/dP} の実 H⁰ と標準単位 uL について、

```lean
def powerRootPrismMonicCompletionPDEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+*
      PrincipalDPPresentation (P ⧸ Ideal.span {(p : P), dP})
        (Ideal.Quotient.mk (Ideal.span {(p : P), dP}) y)
```

を構成した。原典のようにモニック性から mod p 正則性を供給する。
完全 prism から p 局所性・p 正則性・δ(p) の単元性を供給し、
自由性から ghost 射の単射性を供給する。
同 `_coeff` は無限根環 P の全ての元 r について、その実完備化像が
E.frobeniusLift(r) の剰余係数へ送られると述べる。
p の distinguished 性と宇宙を固定する一元族の定義を含め 4 公開宣言を追加した。
f の正次数、prism 商の p 正則性は仮定しない。

BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の台環比較を、
原典とは異なる Witt 座標と階乗表示の経路で進めた段階である。
今回の標準主 pd 表示の係数環は P/(p,dP) と明示している。
既存の R/ϖ 上の実 pd 構造・普遍性との比較には、Frobenius 引戻しの係数作用の
照合が引き続き必要である。原典の T=overline(Δ)_S との同定も未完了。
従ってこれらの同定を完成したとは数えない。


4 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4469 jobs）。新規 20 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4322 宣言の推移的公理依存は標準 3 公理のみ。
主分冪係数商同型と生成元公式、raw p 除算の任意係数商と二元商の pd 同型、
一般の実完備化比較と係数公式、無限根モニック入力の比較と係数公式の
公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.50：ϖ 係数への正確な移送と実完備化剰余の忠実平坦性（検証済み）

新規 `Andre/PowerRootCoefficientIdealQuotient.lean` は、無限根多項式環の
係数主イデアル商の比較を任意の係数イデアル I へ拡張する。
各単項式係数の I への所属で核を I の係数像と同定し、第一同型定理を使う。
係数・単項式・全根変数・通常多項式評価の公式を含め 9 公開宣言を追加した。

新規 `Andre/PerfectPrismFrobeniusPairToVarpi.lean` は、完全 prism W=(A,(d))、
x=φ⁻¹(d)、R=A/(d)、Rv=R/ϖ に対して

```lean
def perfectPrismVarpiToFrobeniusPairEquiv : Rv ≃+* A ⧸ Ideal.span {(p : A), W.generator}
```

を構成した。順写像は代表元 r を φ(r) の二元商へ送り、逆写像は任意の代表元 r を
φ⁻¹(r) の ϖ 商へ送る。これは同 `_symm_mk` で全 r∈A について検証した。
`perfectPrismInverseFrobeniusPolynomial W hW f` は f の全係数を φ⁻¹ で移した
多項式を定義する。この多項式は f とは同一視せず、モニック性の保存だけを証明する。
6 公開宣言を追加した。

新規 `Andre/PowerRootFrobeniusPairVarpiInput.lean` は P=A[Y^(1/p^∞)] の
(p,d) 商と Nv=Rv[Y^(1/p^∞)] の環同型を作る。係数は φ⁻¹ で移り、根変数の番号は保つ。
従って y=f(Y₀) の像は f'=f.map(φ⁻¹) を Rv で評価した入力になる。
単項式・係数・全根変数・通常評価・名前付き入力の像を含め 7 公開宣言を追加した。
この係数変更を省略して元の f の pd 包と同定することはしていない。

新規 `Andre/PowerRootPrismMonicVarpiPDComparison.lean` は、主分冪表示の係数同型を
E1.49 の実完備化比較へ合成する。
E は P の既存 δ 構造、dP と xP は d と x の係数像、L=P{f(Y₀)/dP}、
H=`PDCompletionH0 L p (jL dP)`、uL は標準単位とする。

```lean
def powerRootPrismMonicVarpiCompletionPDEquiv
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    letI := pdCompletionCommRing L p (jL dP)
    (H ⧸ Ideal.span {uL (jL dP), uL (jL xP)}) ≃+*
      PrincipalDPPresentation Nv
        (powerRootPolynomialBaseMap Rv p hp (f'.map barr))
```

ここで barr:A→Rv は自然な係数商射である。
同 `_coeff` は P 全体で Frobenius と入力環比較の合成を明示する。
同 `_base_coeff` は A の係数 r に対し、uL(jL(coeff(r))) の剰余が
右辺の自然な Rv 係数 barr(r) へ送られることを証明する。
源の Frobenius 係数作用と逆係数 Frobenius が相殺する。
標準分冪生成元と一般係数の公式を含め 6 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicVarpiFlat.lean` は、この実商に Rv 係数作用を与える。
台環 S=H/(uL(jL(dP)),uL(jL(xP))) は変更しない。
`powerRootPrismMonicVarpiResidueAlgebra` は主 pd 同型の逆で標準係数作用を戻すが、
同 `_base_coeff` で全 r∈A の像が元の完備化係数像に一致することを検証した。
barr は全射なので、自然な係数作用を特定している。
`powerRootPrismMonicVarpiResidueAlgEquiv` は同じ比較を Rv 代数同型に束ねる。

```lean
theorem powerRootPrismMonicVarpiResidue_free
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    Module.Free Rv S

theorem powerRootPrismMonicVarpiResidue_faithfullyFlat
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := pdCompletionCommRing L p (jL dP)
    letI := powerRootPrismMonicVarpiResidueAlgebra W hW f hf
    Module.FaithfullyFlat Rv S
```

を証明した。逆 Frobenius による係数変更はモニック性と次数を保つため、
既存の Rv 上の主 pd 表示の自由性・忠実平坦性を適用できる。
この工程では prism 商の p 正則性を仮定しない。
係数作用・代数同型・自然係数公式・自由性・忠実平坦性の 5 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の通常平坦性計算の結論を、
原典とは異なる逆 Frobenius 係数入力の経路で実完備化の二元剰余へ移した。
この台環の係数作用と平坦性は明示前提だけで証明済みであり、比較同型は仮定していない。
一方、原典に書かれた元の f の実 pd 包との同定、prismatic 源
T=overline(Δ)_S との同定、T 自体の p 正則性とそこからの完全忠実平坦性の導出は
引き続き未完了。今回の逆係数入力を元の f へ無断で置き換えない。
公開の根付き存在定理には追加仮定・引用を増やしていない。


5 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4474 jobs）。新規 33 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4558 宣言の推移的公理依存は標準 3 公理のみ。
逆係数写像の代表元公式、移送後の入力、ϖ 主 pd 同型と自然係数公式、
係数代数構造の自然係数公式、実完備化剰余の自由性・忠実平坦性の公開型 7 本を
`#check` で確認した（終了コード 0）。


### E1.51：有限 δ 関係商の mod p での次関係の正則性と無限根入力の初期正則対（検証済み）

E1.50 の通常商の自由性だけから、完備化全体の p 正則性を結論しない。
源の正則性を供給するため、有限 raw 関係商で p の正則性と mod p の d 正則性を
同時に保つ帰納法へ進む。次段の δ 関係の最高変数の係数は φ^(N+1)(d) であり、
mod p では d^(p^(N+1)) となる。したがって d が前段 mod p で正則なら
次関係もそこで正則。mod d での次関係の正則性は既存の Witt 正規化で供給できる。
原典の T との同定は別に必要である。

新規 `Andre/DeltaDivisionFiniteModPrimeTail.lean` は、元の自由 δ 環 L₀ の
有限関係イデアル I_N=`deltaDivisionFiniteRelationIdeal D d a N` について、
mod p 商 L₀/((p)+I_N) を初期有限変数の同じ商上の後続多項式環へ分離する。
初期環 B_N=A[σ×Fin(N+1)] の関係イデアルを J_N とすると

```lean
def deltaDivisionFiniteModPrimeTailEquiv :
    (L₀ ⧸ (Ideal.span {(p : L₀)} ⊔ I_N)) ≃+*
      MvPolynomial (σ × ℕ) (B_N ⧸ (Ideal.span {(p : B_N)} ⊔ J_N))
```

である。代表元・係数・次の実 δ 関係の先頭項と下位項の公式を含め
5 公開宣言を追加した。添字族の有限性や源の正則性を仮定しない。

新規 `Andre/DeltaDivisionFiniteModPrimeRegularity.lean` はこの分離を使う。
`deltaFrobeniusIterate_map_of_prime_zero` は p を殺す任意の通常環射 q の下で
q(φ^n(d))=q(d)^(p^n) を計算する。
正則な先頭係数を持つ一次多項式・多変数一次式の正則性と、係数商への正則性の降下から

```lean
theorem deltaDivisionFiniteModPrime_next_regular
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
    (hd : IsSMulRegular (L₀ ⧸ (Ideal.span {(p : L₀)} ⊔ I_N))
      (Ideal.Quotient.mk _ (MvPolynomial.C d))) (s : σ) :
    IsSMulRegular (L₀ ⧸ (Ideal.span {(p : L₀)} ⊔ I_N))
      (Ideal.Quotient.mk _ (deltaDivisionIteratedRelation D d a s (N+1)))
```

を証明した。引用や未知の比較同型を仮定していないが、帰納法の入力 hd は明示している。
さらに `linearMvPolynomial_coefficient_regular_quotient` は、係数環で c が正則、
b が mod c で正則なら、cX-b を課した多項式商でも c が正則と証明する。
この補題は正則対の順序交換を使い、完備性や局所性は要求しない。
6 公開宣言を追加した。

新規 `Andre/PowerRootMonicModPairRegular.lean` は無限根モニック入力へ初期値を供給する。
モニック f の評価は任意の係数イデアル商後も正則であることを、
係数商と無限根環の交換から示す。特に mod(p,d) でも正則となる。
完全 prism W の商 R が p 正則なら、d の mod p 正則性を無限根環の自由性で移す。

`powerRootPrismFirstModPrimeRelation_regular` は、無限根入力環 P に対して
B=P/p、db=d mod p、yb=f(Y₀) mod p と書くと、
B 上の自由変数環で db X_s-yb が正則であることを述べる。
`powerRootPrismMonicFirstModPrime_generator_regular` は、f がモニックなら
その線形関係商でも db の係数像が正則であることを述べる。
これらの初期値のためだけに

```lean
hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)
```

を明示仮定とする。一般の根付き存在定理にこの仮定を追加しない。
係数イデアル商・二元商・二重商の正則性と最初の線形関係を含め
6 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の p ねじれなしの場合の計算を、原典とは異なる
有限 δ 関係商の正則対による帰納法で補完する準備である。
次の工程は、有限段の通常商の mod p を上の一重商へ移す標準同型を整備し、
初期値・次関係の正則性・既存 mod(p,d) Witt 正則性を結んで全有限段へ帰納すること。
その後、有限商の有向余極限による raw 包の p 正則性と、実完備化への保存を示す。
今回、全有限段の正則性・raw 全体の p 正則性・実完備化全体の p 正則性は
まだ証明していない。原典の prismatic 源との比較も引き続き未完了。


3 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4481 jobs）。新規 17 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4624 宣言の推移的公理依存は標準 3 公理のみ。
有限 mod p 分離同型・次関係公式・次関係の正則性、線形関係商での係数正則性、
無限根モニックの二元商正則性・生成元の mod p 正則性・最初の関係とその係数の
正則性の公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.52：全有限 δ 関係商の同時正則性と無限根モニック raw 包の p 正則性（検証済み）

新規 `Andre/RegularTripleQuotientStep.lean` は、任意の可換環で a が正則、
mod a の c,g が正則、さらに mod(a,c) の g が正則なら、g を追加した商でも
a と mod a の c が正則となることを証明する。
正則対の順序交換を二度使い、二重主イデアル商を交換する。
環同型での正則性と自然数 p・mod p の係数正則性の移送を含め 5 公開宣言を追加した。

新規 `Andre/DeltaDivisionFinitePrimeQuotients.lean` は、一元族 a:σ→A（Unique σ）の
有限関係イデアル I_N と通常商 B_N=L₀/I_N について、
B_N/p と L₀/((p)+I_N)、(B_N/p)/d と L₀/((p,d)+I_N) の実同型を構成する。
後者は既存の Witt 正規化が使う一重商そのものである。
深さ零・次段のイデアル式と、一つの次関係を追加する商の同型も構成した。
全ての比較で元の自由環の代表元を保つ。10 公開宣言を追加した。

新規 `Andre/DeltaDivisionFiniteRegularStep.lean` は、D:δ_p A、p 正則な A、
自由 δ 環の ghost 射の単射性、単元 v=δ(d) を明示して、

以下は次段の環とイデアルを Bnext、Inext と略記した型の概略である。

```lean
theorem deltaDivisionUnaryFinite_step_regular
    (hpN : IsSMulRegular B_N (p : B_N))
    (hdN : IsSMulRegular (B_N ⧸ Ideal.span {(p : B_N)})
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I_N (MvPolynomial.C d)))) :
    IsSMulRegular Bnext (p : Bnext) ∧
      IsSMulRegular (Bnext ⧸ Ideal.span {(p : Bnext)})
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk Inext (MvPolynomial.C d)))
```

を証明する。mod p の次関係の正則性は E1.51 の最高係数計算から得る。
mod(p,d) の正則性は、N=0 で既存の第一 jet、N>0 で既存の有限 Witt 計算から得る。
通常二重商へ戻して三元の正則性保存を適用する。3 公開宣言を追加した。

新規 `Andre/DeltaDivisionUnaryFiniteInitialRegular.lean` は、自由 δ 環の mod p を
(A/p) 係数の同じ多項式環と比較し、最初の実関係 dX-a をその線形関係へ移す。
p が A で正則、d が A/p で正則、a が (A/p)/d で正則なら、
最初の関係商でも p と mod p の d が正則と証明する。
この初期段では δ(d) の単元性は不要。比較と代表元公式を含め 7 公開宣言を追加した。

新規 `Andre/DeltaDivisionUnaryRawRegular.lean` は初期段と次段保存を結んだ。
`deltaDivisionUnaryFinite_all_regular` は全ての N に対し上の二つの正則性を同時に証明する。
さらに有限関係イデアルの有向上限による δ 閉包表示を使い、
`deltaDivisionUnaryRaw_relationIdeal_p_saturated` で実 δ 関係イデアルの p 飽和性を示す。
`deltaDivisionUnaryRaw_p_mul_injective` は、その実商 A{a/d} 自体の p 乗算単射性を得る。
前提は A の p 正則性、d mod p の正則性、a mod(p,d) の正則性、
自由 δ 環の ghost 単射性、v=δ(d) の単元性である。
ねじれ除去の新しい商や比較同型の存在を仮定しない。3 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicRawRegular.lean` は完全 prism W の無限根入力 P に適用する。
E は P の既存 δ 構造、dP は生成元の係数像、a は同じ宇宙の一元族 f(Y₀) とする。

```lean
theorem powerRootPrismMonicRaw_p_mul_injective
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (f : Polynomial A) (hf : f.Monic) :
    Function.Injective (fun r : DeltaAdjoinDivision E dP a =>
      (p : DeltaAdjoinDivision E dP a) * r)
```

を証明した。同 `powerRootPrismMonicFinite_all_regular` は全有限段の p 正則性と
mod p の dP 正則性も公開する。ghost 単射性・δ(dP) の単元性・mod(p,dP) の入力正則性は
完全 prism とモニック性から内部で供給する。添字宇宙を固定する自由環の略記を含め
3 公開宣言を追加した。正次数は不要である。

BS Rem 7.15（著者版 p.62）の p ねじれなしの場合を、原典とは異なる有限 δ 関係商の
正則対の同時帰納法と有向上限で計算した段階である。
E1.51 で未完了だった全有限段と raw 包そのものの p 正則性はこの工程で解消した。
prism 商の p 正則性は原典のこの場合の明示仮定であり、一般の公開根付き存在定理へ
追加していない。raw 包の mod p における dP 正則性の有向上限への移送、
実 (p,dP) 完備化での正則性の保存、Hodge–Tate 商の p 正則性、
原典の prismatic 源との同定は引き続き未完了。


6 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4487 jobs）。新規 31 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4821 宣言の推移的公理依存は標準 3 公理のみ。
三元商の正則性保存、有限二重商の比較、次段保存、初期段、全有限段、
一般 raw 包および無限根モニック raw 包の p 正則性など、公開型 8 本を
`#check` で確認した（終了コード 0）。


### E1.53：raw 包の mod p 正則対と実二座標完備化の分母正則性（検証済み）

新規 `Andre/DeltaDivisionUnaryRawPairRegular.lean` は、実 raw 包 L の mod p を
元の自由 δ 環 L₀ の ((p)+J) 商と同定する。J は元の δ 関係イデアルの全 δ 閉包。
比較同型は全ての自由環代表元を保つ。
さらに E1.52 の有限段の mod p の分母正則性を有向上限へ移した。
(p)+J = ⨆ N, ((p)+I_N) と表示し、一有限段で分母を消去する。
`deltaDivisionUnaryRaw_primeIdeal_d_saturated` は (p)+J の分母飽和性、
`deltaDivisionUnaryRaw_mod_prime_d_regular` は実 L/p における分母の正則性を証明する。
前提は E1.52 と同じ、A の p 正則性、d mod p の正則性、a mod(p,d) の正則性、
自由 δ 環の ghost 単射性、δ(d) の単元性。一元添字型 Unique σ を用いる。
4 公開宣言を追加した。

新規 `Andre/PrincipalPairPowerRegular.lean` は一般可換環 R の正則対 b,c について、
b が R で正則、c の像が R/b で正則なら、全ての n について (bⁿ) は c で飽和し、
c の像は R/(bⁿ) で正則となることを証明する。
帰納段では mod b で x=b y とし、b の正則性で一度消して帰納法を適用する。
全座標にこの消去を適用して、古典的 b 完備化でも c の像が正則となる。
`principalPair_adicCompletion_second_regular` の型は

```lean
{R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
(hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c)) :
IsSMulRegular (AdicCompletion (Ideal.span {b}) R)
  (algebraMap R (AdicCompletion (Ideal.span {b}) R) c)
```

である。Noether 性・平坦性・R の完備性は不要。3 公開宣言を追加した。

新規 `Andre/PrincipalPairCompletionRegular.lean` は元の実主完備化 H⁰ と実二座標
完備化 H⁰ へ上の正則性を移す。第一主完備化を既存の標準写像を保つ古典的完備化比較へ
移し、第二元 c が正則なことを得る。その実主 H⁰ を c で再び完備化して正則性を保存し、
既存の反復比較で元の二座標 Koszul 完備化 H⁰ に戻す。
`principalPair_pairCompletion_second_regular` の型は同じ hb,hc の下で

```lean
letI := pairCompletionCommRing R b c
IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c c)
```

である。環構造の乗算と元の加群スカラー作用の一致には、既存の反映の
`mul_scalar_unit` を使う。型の定義上一致を仮定しない。2 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicRawPairRegular.lean` は完全 prism W の無限根モニック入力
P、分母 dP、raw 包 L に適用する。
前提は完全性 hW、prism 商 A/W.ideal の p 正則性 hpR、f のモニック性 hf。
正次数は不要で、一般の公開存在定理へ hpR を追加しない。
`powerRootPrismMonicRaw_mod_prime_generator_regular` は L/p の dL 正則性、
`powerRootPrismMonicRaw_pAdic_regular_pair` は古典的 p 完備化の p と dL の正則性、
`powerRootPrismMonicRaw_pdCompletion_generator_regular` は

```lean
let dL := deltaAdjoinDivisionMap E dP a dP
letI := pdCompletionCommRing L p dL
IsSMulRegular (PDCompletionH0 L p dL) (pdCompletionUnit L p dL dL)
```

を証明する。ここで E,dP,a,L は E1.52 の元の入力・raw 包そのもの。
元の Koszul 完備化と標準射を保持する。3 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の p ねじれなしの場合を、原典とは異なる有限 δ 関係商の
正則対、有向上限、反復主完備化で計算している。
E1.52 で残っていた raw 包の mod p の分母正則性と、実二座標完備化での分母正則性は
この工程で解消した。実二座標完備化の p 正則性、分母を割った Hodge–Tate 商の
p 正則性、原典の prismatic 源との同定は引き続き未完了。

4 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4501 jobs）。新規 12 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4879 宣言の推移的公理依存は標準 3 公理のみ。
raw mod p 比較・分母飽和性・分母正則性、全主冪商・古典的主完備化、実二座標完備化、
無限根モニック入力の二つの完備化に関する公開型 8 本を `#check` で確認した
（終了コード 0）。


### E1.54：実二座標完備化と分母商の p 正則性・通常 p 完備性（検証済み）

新規 `Andre/PrincipalCompletionResidue.lean` は、任意の可換環 R と b∈R に対し、
実主完備化 H⁰ をその標準像 j(b) で割った商と R/(b) の環同型
`principalCompletionResidueEquiv` を構成した。
両剰余で b が零となることから導来完備性を得て、実 H⁰ の環としての一意延長を使う。
順逆合成は元の商射の外延性と一意延長の一意性から確認する。
標準像 j(r) の商を元の代表元 r の商へ送る公式も証明した。
正則性・Noether 性・R の完備性は不要。一般の制限係数作用で像が零の場合の
導来完備性を含め、3 公開宣言を追加した。

新規 `Andre/PrincipalPairCompletionFirstRegular.lean` は正則対 b,c に適用する。
前提は

```lean
{R : Type u} [CommRing R] (b c : R) (hb : IsSMulRegular R b)
(hc : IsSMulRegular (R ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) c))
```

である。第一主完備化の b 正則性を古典的比較で示し、その mod b における c 正則性を
上の実主剰余比較で示す。これが `principalPair_principalCompletion_pair_regular`。
第一主完備化上で順序を交換すると、c が正則で、その c 商で b が正則になる。
E1.53 の一般計算を c,b に適用して、第二主完備化でも b が正則となる。
第二主完備化の c 商は、上の剰余比較で第一主完備化の c 商と同型なので、
そこでも b は正則となる。標準射を保つ既存の反復比較で元の実二座標 H⁰ へ戻す。

公開定理 `principalPair_pairCompletion_first_regular` の結論は

```lean
let := pairCompletionCommRing R b c
IsSMulRegular (PairCompletionH0 R b c) (pairCompletionUnitRingHom R b c b)
```

であり、`principalPair_pairCompletion_mod_second_first_regular` の結論は

```lean
let := pairCompletionCommRing R b c
let j := pairCompletionUnitRingHom R b c
IsSMulRegular (PairCompletionH0 R b c ⧸ Ideal.span {j c})
  (Ideal.Quotient.mk (Ideal.span {j c}) (j b))
```

である。元の Koszul 完備化 H⁰ と標準写像を保持する。3 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicCompletionRegular.lean` は E1.52–53 の元の無限根入力
P、δ 構造 E、分母 dP、一元分子族 a、raw 包 L に適用する。
dL は元の raw 包における dP の標準像、H=PDCompletionH0 L p dL、
uL=pdCompletionUnit L p dL、T=H/(uL(dL)) とする。
完全 prism W、prism 商 A/W.ideal の p 正則性 hpR、f のモニック性 hf の下で、

- `powerRootPrismMonic_pdCompletion_prime_regular`：`IsSMulRegular H (p : H)`。
- `powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular`：`IsSMulRegular T (p : T)`。
- `powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete`：
  `IsAdicComplete (Ideal.span {(p : T)}) T`。

を証明した。最後の主張は実 H⁰ の導来 p 完備性を主商に移し、p 正則性による
古典的完備性との既存比較を適用する。いずれも正次数は不要。
hpR を一般の公開根付き存在定理へ追加しない。3 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の p ねじれなしの場合を、原典とは異なる正則対の
順序交換・反復主完備化の方法で補完した。
E1.53 に残っていた実完備化の p 正則性と Hodge–Tate 候補商の p 正則性は、
この p 正則な prism 商の場合について解消した。
この具体的候補を原典の prismatic 源と同定すること、元の f の Frobenius 引戻しに
関する pd 包同定、通常 ϖ 剰余の既存忠実平坦性からこの候補の p 完全忠実平坦性への
接続は引き続き未完了であり、一般の場合まで完成したとは数えない。

3 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4504 jobs）。新規 9 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 4922 宣言の推移的公理依存は標準 3 公理のみ。
実主剰余比較と係数公式、第一主完備化の正則対、実二座標完備化とその分母商の
正則性、および無限根モニックへの適用の公開型 8 本を `#check` で確認した
（終了コード 0）。


### E1.55：自然な Hodge–Tate 候補の ϖ 完全忠実平坦性と p 完全平坦性（検証済み）

新規 `Andre/PowerRootPrismMonicHodgeTateBase.lean` は、E1.54 の元の実完備化 H と
標準分母商 T=H/(dH) に、prism 商 R=A/W.ideal から自然な基底射
`powerRootPrismMonicHodgeTateBaseMap` を構成した。
元の A 係数射を実完備化へ送り、分母商で W.generator が零となることで降ろす。
全 A 代表元上の公式と、選んだ ϖ が xH の分母商への像となる公式を証明した。
`powerRootPrismMonicHodgeTateVarpiEquiv` は T/(φ(ϖ)) と H/(dH,xH) の環同型であり、
実 H の全代表元を保つ。ここで φ は上の基底射（Frobenius とは別）。
この比較にモニック性も prism 商の p 正則性も不要。5 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicHodgeTateVarpiFlat.lean` は自然な基底射による R 代数構造と、
標準像イデアルによる商の R/ϖ 代数構造を固定する。
像主イデアルを生成元の像の主イデアルへ移して、上の比較を
T/((ϖ).map φ) と既存の H/(dH,xH) の比較へ接続した。
`powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv` は R/ϖ 代数同型であり、
係数上の可換性は R/ϖ の元を A の代表元に戻し、既存の標準係数公式と照合して確認した。
既存の逆 Frobenius 係数変更した pd 表示から得た自由性・忠実平坦性を、この自然な
像イデアル商へ移す。公開した結論は

```lean
powerRootPrismMonicHodgeTateVarpi_free (hf : f.Monic) :
  Module.Free (R ⧸ Ideal.span {ϖ}) (T ⧸ Ideal.map φ (Ideal.span {ϖ}))

powerRootPrismMonicHodgeTateVarpi_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  Module.FaithfullyFlat (R ⧸ Ideal.span {ϖ}) (T ⧸ Ideal.map φ (Ideal.span {ϖ}))
```

である（環・代数構造の let は省略した型表示）。prism 商の p 正則性は不要。
比較先の標準係数構造を同じ明示的商型で固定する補助定義を含め 8 公開宣言を追加した。
巨大な実完備化商の二つの係数構造の照合が必要な代数同型定義に限り、コメント付きで
`maxHeartbeats 2000000` を局所指定した。原典の f の pd 包との同定を済ませたとは扱わない。

新規 `Andre/PowerRootPrismMonicHodgeTateCompletelyFlat.lean` は、同じ正次数モニック入力に
prism 商 R の p 正則性 hpR を明示して適用する。
一般補題 `regular_of_span_power_eq` は正則元 c と bⁿ が同じ主イデアルを生成し n>0 なら
b が正則となることを証明する。(ϖ^p)=(p) を基底 R と基底射の像での T に適用し、
E1.54 の T の p 正則性から、基底および T 上の ϖ 正則性を得る。
自然な ϖ 剰余の忠実平坦性を標準剰余テンソルへ移して正則主元の完全忠実平坦性判定を使う。

公開定理 `powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat` は

```lean
(W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
(hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
(f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
let := pdCompletionCommRing L p dL
let := powerRootPrismMonicHodgeTateAlgebra W hW f
IsCompletelyFaithfullyFlat (Ideal.span {perfectPrismVarpi W hW}) T
```

を証明する。L,dL,H,T は E1.54 と同じ元の実 raw 包・分母・完備化・分母商。
`powerRootPrismMonicHodgeTate_prime_completelyFlat` は同じ前提で
`IsCompletelyFlat (Ideal.span {(p : R)}) T` を証明する。
これは ϖ 完全平坦性を p 乗ねじれの Tor 消滅へ拡張し、(ϖ^p)=(p) を使ったもの。
ϖ 正則性と一般正則性補題を含め 4 公開宣言を追加した。

BS Rem 7.15（著者版 p.62）の通常 pd 剰余計算を、元の係数作用を保ったまま候補 T の
ϖ 完全忠実平坦性へ接続した。原典とは異なる正則対と実反復完備化による経路を明記する。
p 剰余の忠実性の接続、従ってこの具体的候補の p 完全忠実平坦性、
原典の prismatic 源および元の f の Frobenius 引戻し pd 包との同定は引き続き未完了。
条件付きの成果を一般の目標の完成とは数えず、hpR を既存の一般存在定理へ追加しない。

3 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4507 jobs）。新規 17 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5085 宣言の推移的公理依存は標準 3 公理のみ。
自然基底射・ϖ 商比較・係数代数同型・自然剰余の自由性と忠実平坦性・ϖ 正則性・
ϖ 完全忠実平坦性・p 完全平坦性の公開型 8 本を `#check` で確認した
（終了コード 0）。


### E1.56：具体的候補の p 完全忠実平坦性・実根・実完備化 prism（検証済み）

新規 `Andre/FaithfullyFlatNilpotentSquare.lean` は一般の可換環の可換四角形
R→S、B→C、qR:R→B、qS:S→C について、R→S が平坦、B→C が忠実平坦、
qR が全射で核の各元が冪零なら R→S は忠実平坦と証明する。
全ての素イデアルが qR の核を含むので B の素スペクトルから持ち上がり、
B→C のスペクトル全射性を可換性で R→S へ戻す。
qS の全射性や核の一様な冪零指数、Noether 性は不要。1 公開定理を追加した。

新規 `Andre/CompletelyFaithfullyFlatPrincipalPower.lean` は a 完全忠実平坦な可換代数 S に
対し、全ての正冪 aⁿ に関する完全忠実平坦性を証明する。
既存の完全平坦性の冪保存から S/(aⁿ) の R/(aⁿ) 上の平坦性を得る。
R/(aⁿ)→R/(a)、S/(aⁿ)→S/(a) の可換四角形では、左射の核の元を r=a z と表示すると
その n 乗は零となる。上の一般補題で各冪剰余の忠実性を戻す。
標準環商・剰余テンソル比較で完全忠実平坦性の定義へ接続した。

公開定理 `completelyFaithfullyFlat_principal_power_algebra` の型は

```lean
{R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
(hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) (hn : 0 < n) :
IsCompletelyFaithfullyFlat (Ideal.span {a ^ n}) S
```

である。主元の正則性・完備性・Noether 性は不要。
各冪の通常環商の忠実平坦性も公開し、2 公開定理を追加した。

新規 `Andre/PowerRootPrismMonicHodgeTateCompletelyFaithfullyFlat.lean` は E1.55 の同じ元の
候補 T に一般正冪保存を適用し、(ϖ^p)=(p) で書き換えた。
公開定理 `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat` は

```lean
(W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
(hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
(f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
let := pdCompletionCommRing L p dL
let := powerRootPrismMonicHodgeTateAlgebra W hW f
IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T
```

を証明する。L,dL,H,T は E1.54–55 の元の raw 包・分母・実完備化・標準分母商。
自然な基底射と作用を保持したまま、E1.55 に残っていた p 剰余の忠実性を解消した。
prism 商の p 正則性はこの場合の明示仮定であり、一般の公開存在定理へ追加しない。
1 公開定理を追加した。

新規 `Andre/PowerRootPrismMonicHodgeTateRoot.lean` は同じ候補 T 内で、無限根変数 Y₀ の
raw 射・実完備化単位・分母商による標準像を `powerRootPrismMonicHodgeTateRoot` と定義した。
`powerRootPrismMonicHodgeTateRoot_eval` は

```lean
(f.map (Ideal.Quotient.mk W.ideal)).eval₂
  (powerRootPrismMonicHodgeTateBaseMap W hW f)
  (powerRootPrismMonicHodgeTateRoot W hW f) = 0
```

を証明する。raw 関係 dX=f(Y₀) を分母商へ移し、係数射の一致と評価の自然性を使う。
名前付き入力 `powerRootMonicPDInput` は明示的に一度展開する。
この根の計算にモニック性・正次数・prism 商の p 正則性は不要。2 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicCompletionPrism.lean` は、同じ実完備化 H の既存の δ 構造と
標準分母像 dH により `powerRootPrismMonicCompletionPrism` を構成した。
分母の distinguished 性は無限根入力から raw 標準 δ 射と実完備化単位 δ 射で移す。
E1.53 の dH 正則性と実完備化の p,dH 導来完備性を `OrientedPrism.ofDistinguished` へ渡す。
前提は完全 prism W、prism 商の p 正則性 hpR、入力のモニック性 hf。正次数は不要。
元の係数環 A→H の標準射も公開し、δ 構造および指定生成元を保つことを証明した。
4 公開宣言を追加した。完全 prism であることや prismatic envelope の普遍性は主張しない。

BS Rem 7.15（著者版 p.62）の p ねじれなしの場合について、同じ具体的候補に
prism 構造、自然な分母商の p 完全忠実平坦性、元の入力多項式の実根をそろえた。
原典とは異なる正則対・実反復完備化・冪零核での忠実性の経路を明記する。
この経路で原典の prismatic envelope の普遍性と同定すること、元の f に関する
Frobenius 引戻し pd 包同定、および最終完全 δ 化・perfectoid 商との接続は未完了。
条件付きのこの場合を一般の目標の完成とは数えない。

5 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4512 jobs）。新規 10 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5227 宣言の推移的公理依存は標準 3 公理のみ。
冪零核四角形・正冪剰余の忠実平坦性・完全忠実平坦性の正冪保存、具体的候補の
p 完全忠実平坦性・根の評価、実完備化 prism・標準係数射の δ 性・生成元公式の
公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.57：元の実候補の相対普遍性と旧ねじれ除去一段構成への δ 比較（検証済み）

BS 著者版 Prop 7.2（p.55）の証明を再確認した。同証明は raw δ 割り算包の旧分母ねじれの
δ 閉包商を作り、実完備化後の新しい分母ねじれを除く工程を反復する。
本レーンの無限根モニック入力では、元の raw 包の実完備化の分母正則性を E1.53 で
証明しているため、この具体的候補について旧ねじれ除去前後の比較を直接行う。

新規 `Andre/RawDeltaDivisionPDUniversal.lean` は一般の δ 基底 D:δ_p R、分母 d、
分子族 a:σ→R に対して `existsUnique_rawDeltaDivisionPDHom` を証明する。
δ 試験環 E:δ_p T、δ 基底射 f:R→T、f(d) の正則性、全ての f(a_s) の f(d) による
可除性、T の p と f(d) に関する導来完備性を仮定する。
元の raw 包 B=DeltaAdjoinDivision D d a、標準射 j:R→B、
H=PDCompletionH0 B p (j d)、uB=pdCompletionUnit B p (j d) とすれば結論は

```lean
∃! h : H →+* T,
  (deltaPDCompletionStructure (deltaAdjoinDivisionStructure D d a) (j d)).IsDeltaHom E h ∧
    h.comp (uB.comp j) = f
```

である。raw 割り算と実完備化の二つの既存の一意延長を合成する。
源をねじれ除去商に変更せず、試験環の p ねじれも制限しない。1 公開定理を追加した。

新規 `Andre/RawDeltaDivisionPDTorsionComparison.lean` は、元の実 H 上で uB(j(d)) の
乗算が単射であることだけを追加して、旧分母ねじれの δ 閉包商 U の実完備化 HU との
標準環同型 `rawDeltaDivisionPDTorsionEquiv` を構成する。
順射 H→HU は元の raw 包から U→HU への合成を実完備化に延長する。
元の標準 δ 射 B→H は、H の分母正則性により旧ねじれの δ 閉包を殺すため、
U→H へ降りる。この射を実完備化して逆射 HU→H を得る。
両合成は raw 標準射上で一致し、U の商射の全射性と実完備化の環普遍性で恒等射となる。
HU の分母正則性は一切追加仮定しない。
`rawDeltaDivisionPDTorsionEquiv_unit` は全 raw 代表元の標準像を保つことを、
`rawDeltaDivisionPDTorsionEquiv_isDeltaHom` は既存の δ 延長性により δ 構造を保つことを
証明する。逆射の δ 性は順射の δ 性の既存 `IsDeltaHom.symm` から従う。
3 公開宣言を追加した。

新規 `Andre/PowerRootPrismMonicCompletionUniversal.lean` は E1.56 の具体的 prism H に適用する。
入力環 P は元の無限根多項式環、E はその指定 δ 構造、dP は元の prism 生成元の係数像。
完全 prism W、prism 商の p 正則性 hpR、入力モニック性 hf の下で、
`existsUnique_powerRootPrismMonicCompletionHom` は、同じ宇宙の任意の試験 prism Q と
指定した δ 射 g:P→Q について、

```lean
hd : g dP = Q.generator
ha : Q.generator ∣ g (powerRootMonicPDInput p f)
```

なら一意な δ 射 F:H→Q が存在して F.comp(uL.comp jL)=g となることを証明する。
試験 prism の正則性・導来完備性を一般普遍性に渡す。
`powerRootPrismMonicCompletionHom_generator` はこの合成条件から指定生成元も保つことを示す。
これは入力 δ 射を指定した相対的普遍性であり、元の S→Q/(generator) だけからその入力射を
一意に持ち上げる主張をまだ含まない。従って絶対 prismatic envelope の同定とは数えない。

`powerRootPrismMonicCompletionTorsionEquiv` は、この同じ元の実 H を既存の
DerivedDeltaDivisionCompletion E dP a と環同型にする。
係数公式 `powerRootPrismMonicCompletionTorsionEquiv_coeff` と
δ 性 `powerRootPrismMonicCompletionTorsionEquiv_isDeltaHom` も公開した。
自分自身の分母正則性を一般比較へ供給するため、比較同型の存在を仮定しない。
このファイルに 5 公開宣言を追加した。正次数は不要であり、hpR を一般の公開存在定理へ追加しない。

原典 Prop 7.2（p.55）、Rem 7.15（p.62）の raw・旧ねじれ除去・実完備化の比較を、
本レーンの正則性により反復なしの具体的一段について補完した。原典と異なる経路を明記する。
元の S の写像からの入力 δ 射の一意持上げと絶対 envelope の同定、元の f に関する
Frobenius 引戻し pd 包の同定、およびこの経路での最終完全 δ 化・perfectoid 商との接続は未完了。

3 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4517 jobs）。新規 9 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5333 宣言の推移的公理依存は標準 3 公理のみ。
一般 raw 普遍性・旧ねじれ除去比較と代表元公式・δ 性、具体的相対普遍性・比較同型・
δ 性・生成元保存の公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.58：元の実候補の完全 δ 化後の perfectoid 商と標準根（検証済み）

新規 `Andre/RawDivisionPDPerfectionComparison.lean` は、B4-6 の
DeltaRootPDCompletedPerfectionComparison のうち根方程式の形を使わない比較を、
任意の δ 基底 D:δ_p A、分母 d、分子族 a:σ→A に一般化した。
Raw=DeltaAdjoinDivision D d a、F=deltaAdjoinDivisionStructure D d a、
ι=deltaAdjoinDivisionMap D d a、z=ι(d)、S=PDCompletionH0 Raw p z とする。
S の指定 δ 構造 G を δ 完全化して C=DeltaPerfection G とし、
x=deltaPerfectionOf G 0 (pdCompletionUnit Raw p z z) と置く。
H=PDCompletionH0 C p x、s=pdCompletionUnit C p x とすれば、
`rawDivisionPDPerfectionEquiv` は

```lean
H ≃+* DivisionPrismCarrier D d a
```

を構成する。既存の δ 完全化・実完備化順序交換の逆と、p 完備化先行比較を合成する。
元の raw 包からの全標準係数射、指定分母像を保ち、順逆両方向とも δ 射であることを証明した。
分子族の形・モニック性・分母正則性に依存しない。
分母が distinguished なら主生成元商の比較
`rawDivisionPDPerfectionQuotientEquiv` は

```lean
(H ⧸ Ideal.span {s x}) ≃+* DivisionPerfectoidCandidate D d a hd
```

を与え、元の A 係数射を保つ。
`rawDivisionPDPerfectionQuotient_isIntegralPerfectoid` は同じ源商の整 perfectoid 性を
既存の完全 prism 商から移す。全代表元上の商公式を含め 8 公開宣言を追加した。
この環同型だけから源の実完備化の忠実平坦性が最終商へ移るとは主張しない。

新規 `Andre/PowerRootPrismMonicCompletedPerfection.lean` は同じ構成を、E1.54–57 の
元の無限根入力 P、δ 構造 E、分母 dP、一元分子族 a、raw 包 L、その実完備化 H に適用する。
DH を H の指定 δ 構造、C=DeltaPerfection DH、x=deltaPerfectionOf DH 0 dH とし、
H∞=PDCompletionH0 C p x、T∞=H∞/(pdCompletionUnit C p x x) とする。
`powerRootPrismMonicCompletedPerfectionQuotientEquiv` は T∞ と既存の
DivisionPerfectoidCandidate E dP a の標準環同型を与える。
`powerRootPrismMonicCompletedPerfectionQuotientEquiv_coeff` は P の全ての元の標準像を保つ。
`powerRootPrismMonicCompletedPerfection_isIntegralPerfectoid` の結論は

```lean
let := pdCompletionCommRing L p dL
let := pdCompletionCommRing C p x
IsIntegralPerfectoid T∞ p
```

である。完全 prism W を前提とするが、入力のモニック性・正次数・prism 商の p 正則性は不要。

`powerRootPrismMonicHodgeTateToCompletedPerfection` は、元の T=H/(dH) から T∞ への自然射を
構成する。δ 完全化・再完備化の標準射が dH を殺すので通常商へ降ろす。
その合成で `powerRootPrismMonicCompletedPerfectionBaseMap` を定め、
`powerRootPrismMonicCompletedPerfectionRoot` は元の T の指定根の標準像とする。
`powerRootPrismMonicCompletedPerfectionRoot_eval` は

```lean
(f.map (Ideal.Quotient.mk W.ideal)).eval₂
  (powerRootPrismMonicCompletedPerfectionBaseMap W hW f)
  (powerRootPrismMonicCompletedPerfectionRoot W hW f) = 0
```

を証明した。環射に沿う根の移送は一般補題 `polynomialRoot_mapRingHom` に分離した。
自然射の型検査では先に元の δ 構造と標準完全化射を固定し、二つの巨大な実 H⁰ の環構造の
照合を減らした。同自然射の定義に限りコメント付きで `maxHeartbeats 2000000` を局所指定した。
このファイルに 8 公開宣言を追加した。

BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の完全化・perfectoid 商への接続について、
元の具体的実完備化と同じ係数射・根を使う経路をそろえた。原典とは異なる順序比較を明記する。
元の T の p 完全忠実平坦性を、この完全化に沿う基底上の T∞ の p 完全忠実平坦性へ
保存する証明は引き続き未完了。自然射 T→T∞ 自体の忠実平坦性を仮定も結論もしない。
次の接続では、元の H の (p,d) 導来剰余を正則対と T の p 完全忠実平坦性から計算し、
既存の完全 δ 基底に対する Frobenius 段・余極限の剰余忠実平坦性へ渡す必要がある。
絶対 prismatic envelope の同定と、元の f の Frobenius 引戻し pd 包の同定も未完了であり、
この perfectoid 性と根だけで一般存在目標の完成とは数えない。

2 対象および集約の `set -o pipefail; lake build` は終了コード 0
（集約 4519 jobs）。新規 16 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5461 宣言の推移的公理依存は標準 3 公理のみ。
一般比較・両方向の δ 性・商の係数保存・perfectoid 性、具体的な自然射・perfectoid 性・
根の評価・全入力係数の保存の公開型 8 本を `#check` で確認した（終了コード 0）。


### E1.59 正則主剰余から元の実完備化の二元完全平坦性と導来離散性（2026-10-17）

新規 `Andre/CompletelyFlatRegularReduction.lean` は、任意イデアル I の完全平坦な
加群 M の標準 I 剰余の高次 Tor 消滅を証明した。
`scalarExtensionTorVanishing_of_completelyFlat` はイデアルで消える商基底自体を
試験加群に取り、Tor の対称性で実際の制限スカラー加群へ移す。

`completelyFlat_pair_of_regular_principal_reduction` の型は、R を可換環、
M : ModuleCat R、q : R →+* R/(d) と書けば

```lean
(a d : R) (hd : IsSMulRegular R d)
(M : ModuleCat R) (hMd : IsSMulRegular M d)
(hred : IsCompletelyFlat (Ideal.span {q a})
  ((ModuleCat.extendScalars q).obj M)) :
IsCompletelyFlat (Ideal.span {a, d}) M
```

である。正則主剰余の Tor 非輪状性と底変換を使う。
新規 `Andre/CompletelyFlatRegularAlgebraReduction.lean` は通常主環商と標準加群
スカラー拡大の線形同型を公開し、同じ判定を代数 S の通常商 S/(dS) に移す。
この二つのファイルに各 2 公開宣言を追加した。完備性や Noether 性は仮定しない。

新規 `Andre/PowerRootPrismMonicCompletionPairFlat.lean` は E1.54–58 と同じ
W : OrientedPrism p A、hW : W.deltaStructure.IsPerfect、一元モニック f : Polynomial A、
無限根多項式環 P、δ 除算包 L とその標準射 jL、
H = PDCompletionH0 L p (jL dP)、その標準単位 uL を使う。
c = powerRootPrismMonicCompletionBaseMap W hW f : A →+* H とする。
`powerRootPrismMonicCompletionAlgebra` は c.toAlgebra そのものである。
自然な H/dH の既存の R=A/W.ideal 作用が標準主環商作用と等しいことを
`powerRootPrismMonicHodgeTateAlgebra_eq_principal` で全代表元上証明した。

`powerRootPrismMonicCompletion_pair_completelyFlat` の正確な結論は

```lean
let := pdCompletionCommRing L p (jL dP)
let := powerRootPrismMonicCompletionAlgebra W hW f
IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H
```

であり、追加引数は
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)`、
`hf : f.Monic`、`hdeg : 0 < f.natDegree`。
W.generator の基底環と H 上の正則性、および同じ自然な H/dH の p 完全平坦性から従う。

`powerRootPrismMonicCompletionScalarEquiv` は
`baseChangeScalarModule c ≃ₗ[A] H` を与える。
`powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing` は同じ hpR/hf/hdeg の下で

```lean
scalarExtensionTorVanishing
  (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))
  (baseChangeScalarModule c)
```

を証明する。q₂ = Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})、
M = baseChangeScalarModule c、Q = A/(p,d) と書くと
`powerRootPrismMonicCompletion_pair_reduction_homology_isZero` は任意 i : ℤ、hi : i ≠ 0 に対し

```lean
IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
  ((boundedAboveDerivedBaseChange q₂).obj
    (boundedAboveDerivedSingleFunctor.obj M)).obj)
```

を与える。H の環構造の let を型に明示している。ここまで具体的ファイルは 6 公開宣言。
BS Rem 7.15（著者版 p.62）の導来剰余を、原典とは異なる正則主剰余と Tor 底変換で計算した。

この工程はまだ H の導来 (p,d) 剰余 H⁰ の忠実平坦性を証明していない。
次に同じ自然な H/dH の p 完全忠実平坦性からその H⁰ の忠実平坦性を移し、
既存の δ 完全化の剰余忠実平坦性へ渡す必要がある。
元の完成後 perfectoid 候補の p 完全忠実平坦性、絶対 prismatic envelope の同定、
元の f に対する Frobenius 引戻し pd 包の同定は未完了。
hpR を既存の任意族存在定理へ追加しておらず、これらの条件付き中間結果を完成と数えない。

3 対象を含む対象ビルドと集約の `set -o pipefail; lake build` は終了コード 0
（集約 4526 jobs）。新規 10 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5520 宣言の推移的公理依存は標準 3 公理のみ。
一般主剰余判定・代数版・具体的二元完全平坦性・実制限加群の Tor 消滅・
導来剰余の非零次数消滅の公開型 5 本を `#check` で確認した（終了コード 0）。


### E1.60 元の導来剰余 H⁰ の忠実平坦性と完全 δ 化後への保存（2026-10-17）

新規 `Andre/CompletelyFaithfulPairReduction.lean` に 2 公開宣言を追加した。
`scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat` は任意の可換環 R、
I : Ideal R、M : ModuleCat R について、IsCompletelyFaithfullyFlat I M から
標準 I 剰余スカラー拡大の忠実平坦性を与える。
`pairScalarExtension_faithfullyFlat_of_principal_reduction` の正確な型は
q_d = Ideal.Quotient.mk (Ideal.span {d}) と書くと

```lean
(a d : R) (M : ModuleCat R)
(hred : IsCompletelyFaithfullyFlat (Ideal.span {q_d a})
  ((ModuleCat.extendScalars q_d).obj M)) :
Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a, d}))).obj M)
```

である。通常二重主商の同型に沿う底変換で忠実平坦性を移し、
スカラー拡大合成の自然同型で元の二元剰余に戻す。正則性や完備性は不要。

新規 `Andre/PowerRootPrismMonicCompletionPairFaithful.lean` は E1.59 と同じ
完全 prism W : OrientedPrism p A、hW、f : Polynomial A、L、jL、dP、
H = PDCompletionH0 L p (jL dP)、c = powerRootPrismMonicCompletionBaseMap W hW f
を使う。仮定は E1.59 と同じ

```lean
(hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
(hf : f.Monic) (hdeg : 0 < f.natDegree)
```

である。Q = A ⧸ Ideal.span {(p : A), W.generator}、q : A →+* Q を標準射、
M = baseChangeScalarModule c と書くと
`powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat` は

```lean
let := pdCompletionCommRing L p (jL dP)
Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M)
```

を証明する。自然な H/dH の完全忠実平坦性を標準主環商作用へ移し、
実制限加群と通常 H の線形同型、主商の標準スカラー拡大比較を合成して一般判定に渡した。
`powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat` の結論は

```lean
let := pdCompletionCommRing L p (jL dP)
Module.FaithfullyFlat Q
  ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
    ((boundedAboveDerivedBaseChange q).obj
      (boundedAboveDerivedSingleFunctor.obj M)).obj)
```

である。標準 H⁰ 比較の線形同型を使い、係数作用を変えていない。
E1.59 の非零次数消滅と合わせ、元の H の導来二元剰余入力がそろった。

新規 `Andre/PowerRootPrismMonicPerfectionPairFaithful.lean` では
DH = deltaPDCompletionStructure (deltaAdjoinDivisionStructure E dP a) (jL dP)、
C = DeltaPerfection DH、κ = deltaAlgebraPerfectionCoefficient DH c、
H′ = PDCompletionH0 C p (κ W.generator)、
t = (pdCompletionUnit C p (κ W.generator)).comp κ、M′ = baseChangeScalarModule t、
Y′ = (boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M′)
と固定する。前提は同じ W/hW/hpR/f/hf/hdeg であり、次の 3 公開定理を追加した。
各型の先頭には元の H と H′ の `pdCompletionCommRing` を let で明示する。

- `powerRootPrismMonicCompletedPerfection_pair_homology_isZero`：任意 i : ℤ、hi : i ≠ 0 に対し
  `IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj Y′.obj)`。
- `powerRootPrismMonicCompletedPerfection_pairH0_faithfullyFlat`：
  `Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y′.obj)`。
- `powerRootPrismMonicCompletedPerfection_pair_completelyFaithfullyFlat`：
  `IsCompletelyFaithfullyFlat (Ideal.span {(p : A), W.generator}) (ModuleCat.carrier M′)`。

元の標準係数射 c の δ 性と実剰余入力を既存の
`perfectPrismDeltaAlgebraPD_*` の一般判定へ渡した。
BS Rem 7.15（著者版 p.62）の完全化後の平坦性保存を、原典とは異なる
正則主剰余・Tor 底変換と完全 δ 基底での Frobenius 段・余極限の経路で証明した。
新しい引用・公理・sorry は追加していない。

最終の生成元商への p 完全忠実平坦性の移送、hpR を仮定しない原典経路の補完、
絶対 prismatic envelope の同定、元の f の Frobenius 引戻し pd 包の同定は未完了。
E1.58 の具体的な完全化後商・自然基底射との比較も次工程で係数作用を検証する必要がある。
本工程の条件付き結果を全体の完成とは数えず、承認済み hdeg を持つ任意族存在定理の型も変えない。

3 対象を含む対象ビルドと集約の `set -o pipefail; lake build` は終了コード 0
（集約 4529 jobs）。新規 7 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5642 宣言の推移的公理依存は標準 3 公理のみ。
新規 7 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.61 正則生成元商への完全忠実平坦性の下降（2026-10-17）

新規 `Andre/RegularQuotientCompleteFaithful.lean` の
`completelyFaithfullyFlat_principal_quotient_of_pair` は可換環 A、自然数 p、d : A、
A 代数 S に対し、正確に次を証明する。商の作用は
`principalAdicQuotientAlgebra d S` を局所インスタンスとして固定する。

```lean
(p : ℕ) (d : A) (hd : IsSMulRegular A d)
(S : Type u) [CommRing S] [Algebra A S]
(hSd : IsSMulRegular S (algebraMap A S d))
(hS : IsCompletelyFaithfullyFlat (Ideal.span {(p : A), d}) S) :
IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {d})})
  (S ⧸ Ideal.span {algebraMap A S d})
```

正則主剰余の標準増大同型と通常商のスカラー拡大比較を合成する。
元の二元剰余の離散性と H⁰ の忠実平坦性を二段階剰余へ移し、
商上の p 完全忠実平坦性の定義へ戻す。p の素数性・完備性・Noether 性は不要。

新規 `Andre/PerfectedDeltaAlgebraQuotientFaithful.lean` は
P : OrientedPrism p A、E : DeltaStructure p B、j : A →+* B に対する一般判定。
C=DeltaPerfection E、κ=deltaAlgebraPerfectionCoefficient E j、R=A/(P.generator)
とする。任意の b : C と hb : κ P.generator = b に対し
`perfectedDeltaAlgebraQuotientBaseMap` は

```lean
let := pdCompletionCommRing C p b
R →+* (PDCompletionH0 C p b ⧸ Ideal.span {pdCompletionUnit C p b b})
```

を通常主商への降下射として構成する。
`perfectedDeltaAlgebraQuotientBaseMap_mk` は元の A の任意の代表元を
`Ideal.Quotient.mk _ (pdCompletionUnit C p b (κ r))` に送ることを証明する。

`perfectedDeltaAlgebraQuotientBaseMap_completelyFaithfullyFlat` の結論は
上記の環射を g_b、商を T_b と書くと

```lean
let := pdCompletionCommRing C p b
let := g_b.toAlgebra
IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T_b
```

である。引数は P、E、j、P.deltaStructure.IsPerfect、P.deltaStructure.IsDeltaHom E j と、
同じ j の実導来 (p,P.generator) 剰余の全非零次数消滅・H⁰ の忠実平坦性、b、hb。
これらの実剰余入力の型は既存の `perfectPrismDeltaAlgebraPD_*` と同じ形を保つ。
b の等式で標準生成元表記へ戻し、完全 δ 環の実完備化 prism の正則性と二元完全忠実平坦性を
一般の主商下降判定へ渡す。自然な係数射の作用は標準主商代数作用と代表元上で一致する。

新規 `Andre/PowerRootPrismMonicPerfectionQuotientFaithful.lean` は E1.60 と同じ
W : OrientedPrism p A、hW、無限根多項式環 P と δ 構造 E、dP、分子族 a、
raw 包 L と射 jL、実完備化 H、DH、c : A →+* H を使う。
C=DeltaPerfection DH、x=deltaPerfectionOf DH 0 (pdCompletionUnit L p (jL dP) (jL dP))、
H∞=PDCompletionH0 C p x、sC=pdCompletionUnit C p x、T∞=H∞/(sC x) とする。
これは E1.58 の具体的な最終商と同じ対象。

`powerRootPrismMonicPerfectionAlgebra` は標準射
`(sC.comp (deltaAlgebraPerfectionCoefficient DH c)).toAlgebra : Algebra A H∞` を固定する。
`powerRootPrismMonicPerfection_generator_regular` は同じ標準射による W.generator の像が
H∞ 上正則であることを証明する。モニック性・正次数・prism 商の p 正則性はここには不要。

`powerRootPrismMonicCompletedPerfectionBaseMap_completelyFaithfullyFlat` は
E1.58 の自然な基底射 g=powerRootPrismMonicCompletedPerfectionBaseMap W hW f に対し
正確に次を結論する。

```lean
let := pdCompletionCommRing L p (jL dP)
let := pdCompletionCommRing C p x
let := g.toAlgebra
IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞
```

引数は W、hW、および
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)`、
f : Polynomial A、hf : f.Monic、hdeg : 0 < f.natDegree。
E1.59–60 の実剰余入力を一般判定に渡し、一般の基底射と g の一致を
`Ideal.Quotient.ringHom_ext` により元の A の係数上で証明する。
商の代表元を文脈全体で置換する方法は巨大なホモロジーの定義展開を招くので採らない。
係数射を引数にする完全忠実平坦性の述語に射の等式を適用し、依存する作用も移す。

BS Rem 7.15（著者版 p.62）の一元根付き候補について、原典とは異なる
Tor 底変換と完全 δ 化の剰余計算を用いる経路である。新しい引用・公理・sorry は追加しない。
prism 商の p 正則性仮定を解消する原典経路、絶対 prismatic envelope の同定、
元の f の Frobenius 引戻し pd 包の同定は引き続き未完了。
この条件付き一元結果を任意族の原典経路の完成とは数えず、既存の承認済み hdeg を持つ
任意族存在定理の型を変更しない。

3 対象を含む対象ビルドと集約の `set -o pipefail; lake build` は終了コード 0
（集約 4532 jobs）。新規 7 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5739 宣言の推移的公理依存は標準 3 公理のみ。
新規 7 公開宣言の正確な型を `#check` で確認した（終了コード 0）。
一時的な診断設定と拡大した heartbeat 上限は保存コードから全て除いた。


### E1.62 係数 Frobenius に沿う実テンソル底変換と元の mod p 入力の pd 包（2026-10-17）

BS Rem 7.15（著者版 p.62）の画像と本文を再確認した。
既存の明示係数 Frobenius 同型の向きは e : R/ϖ ≃+* R/p であり、A の元 a に対して
`e (a mod (d,ϖ)) = φ_A(a) mod (d,p)` である。
これを使って逆 Frobenius 係数の f′ を元の f の mod p 像に戻す。
本工程では底環を R/p と明示し、R/ϖ と R/p や二つの入力を暗黙に同一視しない。

新規 `Andre/SemilinearTensorBaseChange.lean` に 2 公開宣言を追加した。
`tensorBaseChangeAlgEquivOfSemilinearRingEquiv` は任意の可換環 R,S,B,C、
Algebra R B、Algebra S C、e : R ≃+* S、F : B ≃+* C と

```lean
(hF : ∀ r : R, F (algebraMap R B r) = algebraMap S C (e r)) :
let := e.toRingHom.toAlgebra
S ⊗[R] B ≃ₐ[S] C
```

を構成する。順射はテンソル普遍射、逆射は c ↦ 1⊗F⁻¹(c)。
`tensorBaseChangeAlgEquivOfSemilinearRingEquiv_tmul` は s⊗b を
`algebraMap S C s * F b` に送ることを証明する。
平坦性・標数・正則性・非零性は不要。

新規 `Andre/PowerRootVarpiPrimeFrobeniusPD.lean` に 8 公開宣言を追加した。
W : OrientedPrism p A、hW : W.deltaStructure.IsPerfect、f : Polynomial A とする。
R=A/W.ideal、Rv=R/(perfectPrismVarpi W hW)、Rp=R/p、
Nv=PowerRootPolynomial Rv p hp、Np=PowerRootPolynomial Rp p hp、
bv : A →+* Rv、bp : A →+* Rp を通常の二段商射、
f′=perfectPrismInverseFrobeniusPolynomial W hW f と書く。
zv=powerRootPolynomialBaseMap Rv p hp (f′.map bv)、
zp=powerRootPolynomialBaseMap Rp p hp (f.map bp)、
Dv=PrincipalDPPresentation Nv zv、Dp=PrincipalDPPresentation Np zp とする。

`varpiPrimeFrobenius_inverse_coeff` は `e (bv (φ_A⁻¹(a))) = bp a` を証明する。
`powerRootVarpiPrimeFrobeniusEquiv : Nv ≃+* Np` は変数を固定する係数環同型。
係数・全根変数上の公式と `powerRootVarpiPrimeFrobeniusEquiv_input` の結論
`powerRootVarpiPrimeFrobeniusEquiv W hW zv = zp` を証明した。
`powerRootVarpiPrimeFrobeniusPDEquiv : Dv ≃+* Dp` はこの入力同型を持ち上げる。
同 pd 同型の係数公式と全標準分冪生成元の次数を保つ公式も公開した。
このファイルにはモニック性・次数・prism 商の p 正則性仮定はない。

新規 `Andre/PowerRootPrismMonicFrobeniusBaseChange.lean` に 4 公開宣言を追加した。
E1.55–61 と同じ raw 包 L、その実完備化 H と標準射 uL,jL、dP と ϖ 持上げ xP を使う。
T=H/(uL(jL dP))、φ=powerRootPrismMonicHodgeTateBaseMap W hW f、
Iv=Ideal.span {perfectPrismVarpi W hW}、Mv=T ⧸ Ideal.map φ Iv とする。
Mv は元の T の自然な ϖ 商であり、係数作用は
`powerRootPrismMonicHodgeTateVarpiAlgebra W hW f` そのもの。

`powerRootPrismMonicVarpiFrobeniusResidueEquiv (hf : f.Monic)` は
元の Mv ≃+* Dp を構成し、係数公式は

```lean
powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f hf (algebraMap Rv Mv r) =
  algebraMap Rp Dp (e r)
```

である。二重商と二元商の既存 Rv 代数同型、逆係数入力の pd 表示、係数 Frobenius を合成した。
`powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv` の正確な型は

```lean
(hf : f.Monic) :
let := pdCompletionCommRing L p (jL dP)
let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
let := e.toRingHom.toAlgebra
Rp ⊗[Rv] Mv ≃ₐ[Rp] Dp
```

である。`powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_tmul` は
任意の r : Rp、m : Mv を含む単純テンソルの値を
`algebraMap Rp Dp r * powerRootPrismMonicVarpiFrobeniusResidueEquiv W hW f hf m`
と指定する。これらの実底変換同型には正次数・prism 商の p 正則性は不要。

新規 `Andre/PowerRootPrimeFrobeniusPDEnvelope.lean` に 3 公開宣言を追加した。
`powerRootPrimeFrobeniusDividedPowers` は
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)` と hf : f.Monic の下で
`DividedPowers (principalDPPositiveIdeal zp)` を構成する。
逆係数入力の実分冪構造を、入力を保つ係数環同型で移送する。
`powerRootPrimeFrobeniusDividedPowers_base_apply` は任意 n : ℕ に対し
入力 zp の n 次分冪が principalDPGenerator zp n に一致することを証明する。
`existsUnique_powerRootPrimeFrobeniusPDMorphism` は任意宇宙の可換環 B と Algebra Np B、
I : Ideal B、Ht : DividedPowers I、hzB : algebraMap Np B zp ∈ I に対し、

```lean
∃! F : Dp →ₐ[Np] B,
  (powerRootPrimeFrobeniusDividedPowers W hW f hpR hf).IsDPMorphism Ht F.toRingHom
```

を証明する。標的のねじれ・完備性・非零性には条件を加えない。

これは原典とは異なる、既存の Witt 座標比較・係数環同型・通常テンソルを経る証明。
元の f の mod p 入力と実分冪包への係数比較を前進させたが、
A 上の φ_A 引戻し全体との同定、Np の自然な作用の根変数上の照合、原典の R/ϖ 表記との
最終照合はまだ残る。prism 商の p 正則性仮定の解消と絶対 prismatic envelope の同定も未完了。
これらを実底変換同型だけから完成したと数えない。承認済み hdeg を持つ存在定理の型は変更しない。

4 対象を含む対象ビルドと集約の `set -o pipefail; lake build` は終了コード 0
（集約 4536 jobs）。新規 17 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 5947 宣言の推移的公理依存は標準 3 公理のみ。
新規 17 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.63 実 Frobenius テンソルの自然な根変数作用と実 pd 普遍性（2026-10-17）

E1.62 と同じ完全 prism W : OrientedPrism p A、hW、f : Polynomial A を固定する。
P、L、jL、H、uL、dP、ϖ 持上げ xP は既存の無限根モニック raw 候補のもの。
R=A/W.ideal、Rv=R/ϖ、Rp=R/p、e : Rv ≃+* Rp は指定係数 Frobenius 同型、
T=H/(uL(jL dP))、φ : R →+* T は自然な基底射、Mv=T/(Ideal.map φ (ϖ)) とする。
Np=PowerRootPolynomial Rp p hp、zp=powerRootPolynomialBaseMap Rp p hp (f.map bp)、
Dp=PrincipalDPPresentation Np zp とし、bp : A →+* Rp は標準二段商射。
Ft=Rp ⊗[Rv] Mv には e.toRingHom.toAlgebra と元の自然な Mv 作用を使う。
以下の実対象の公開型では H の `pdCompletionCommRing` と必要な代数作用を let で明示する。

新規 `Andre/PowerRootPrismMonicFrobeniusRootAction.lean` に 4 公開宣言を追加した。
`powerRootPrismMonicVarpiInputMap` は元の P から Mv への自然な射 ψ を
raw 射・実完備化単位・生成元商・自然な ϖ 商の合成として定義する。
`powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable` は E1.62 の半線形比較 U に対し

```lean
U (ψ (powerRootPolynomialVariable A p hp n)) =
  algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n) ^ p
```

を証明した。同 `_variable_succ` は元の第 n+1 根変数の像を
比較先の第 n 根変数の係数像へ送ることを示す。
`powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable` は実テンソル比較 E に対し

```lean
E ((1 : Rp) ⊗ₜ[Rv] ψ (powerRootPolynomialVariable A p hp (n + 1))) =
  algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n)
```

を証明する。実比較の全係数公式と変数 Frobenius・隣接根関係、単純テンソル公式を使う。
いずれも W/hW/f に加えて hf : f.Monic のみを仮定し、p 正則性や正次数は不要。

新規 `Andre/PrincipalPDSourceTransport.lean` に 8 公開宣言を追加した。
任意の可換環 A、y : A、A 代数 B、eB : B ≃ₐ[A] PrincipalDPPresentation A y に対し、
`principalPDSourceIdeal` は標準正次数イデアルを eB⁻¹ で写した B のイデアルを定義する。
`principalPDSourceDividedPowers` は比較先の実分冪構造をこのイデアルへ戻す。
入力元の所属、順逆両方の分冪射性、入力元の全分冪の値を証明し、
`existsUnique_principalPDSourceMorphism` は比較先の標準値の公式を前提として
B から任意宇宙の分冪標的への A 代数分冪射の一意存在を与える。
`principalPDSourcePolynomialEvaluation` は係数環 K の作用の可換性と入力変数の像を
明示引数にし、同型の源における通常多項式の評価を比較先で計算する。
この一般層の係数可換性は具体的適用で全て証明しており、未証明の仮定には残さない。

新規 `Andre/PowerRootPrismMonicFrobeniusTensorAlgebra.lean` に 6 公開宣言を追加した。
`powerRootPrismMonicFrobeniusTensorInputAlgebra` は E⁻¹ と Np の標準係数射の合成から
Ft の Np 代数構造を定める。この作用について次の自然な像を証明した。

```lean
algebraMap Np Ft (algebraMap Rp Np r) = algebraMap Rp Ft r
algebraMap Np Ft (powerRootPolynomialVariable Rp p hp n) =
  (1 : Rp) ⊗ₜ[Rv] ψ (powerRootPolynomialVariable A p hp (n + 1))
```

公開名はそれぞれ
`powerRootPrismMonicFrobeniusTensorInputAlgebra_coeff` と同 `_variable`。
`powerRootPrismMonicFrobeniusTensorInputAlgEquiv` は E と同じ環同型を Np 代数同型へ強める。
`powerRootPrismMonicFrobeniusTensorInputScalarTower` は元の Rp 作用と Np 作用の塔を与える。
同 `_InputAlgebra_polynomial` は任意の g : Polynomial Rp に対し

```lean
algebraMap Np Ft (powerRootPolynomialBaseMap Rp p hp g) =
  g.eval₂ (algebraMap Rp Ft)
    ((1 : Rp) ⊗ₜ[Rv] ψ (powerRootPolynomialVariable A p hp 1))
```

を証明した。従って元の f の mod p 入力の像も、元の第一根変数の像とのテンソルにおける
通常評価そのものである。作用を移送しただけで自然性を未確認のままにはしていない。
これらの自然な作用の結果は hf のみを前提とし、p 正則性・正次数を仮定しない。

新規 `Andre/PowerRootPrismMonicFrobeniusTensorPD.lean` に 6 公開宣言を追加した。
E_N : Ft ≃ₐ[Np] Dp を上記の自然な入力環上の比較とし、
J=(principalDPPositiveIdeal zp).map E_N.symm.toRingHom とする。
`powerRootPrismMonicFrobeniusTensorPDIdeal` は同じ Ft のこのイデアル J を固定する。
入力像 algebraMap Np Ft zp の J への所属は hf のみの下で証明した。

`powerRootPrismMonicFrobeniusTensorDividedPowers` は hf と
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)` の下で
`DividedPowers J` を構成する。
`powerRootPrismMonicFrobeniusTensorInputAlgEquiv_isDPMorphism` は E_N の実分冪射性を証明する。
`powerRootPrismMonicFrobeniusTensorDividedPowers_input_apply` は全 n : ℕ について

```lean
(powerRootPrismMonicFrobeniusTensorDividedPowers W hW f hf hpR).dpow n
  (algebraMap Np Ft zp) = E_N.symm (principalDPGenerator zp n)
```

を証明する。正次数や非零性の仮定は加えない。

`existsUnique_powerRootPrismMonicFrobeniusTensorPDMorphism` の引数は
W、hW、f、hf、hpR、任意宇宙の可換環 B と Algebra Np B、I : Ideal B、
Ht : DividedPowers I、hzB : algebraMap Np B zp ∈ I。
正確な結論は必要な既存の環構造・三つの代数作用を let で導入した後の

```lean
∃! F : Ft →ₐ[Np] B,
  (powerRootPrismMonicFrobeniusTensorDividedPowers W hW f hf hpR).IsDPMorphism
    Ht F.toRingHom
```

である。標的のねじれ・完備性・非零性には条件を課さない。
これにより、自然な根変数作用を持つ実テンソルそのものが、元の mod p 入力の pd 包の
普遍性を持つことまで進めた。BS Rem 7.15(1)（著者版 p.62）に対する原典とは異なる
Witt 座標・半線形環同型・通常テンソル・実分冪構造の移送を用いる経路である。

E1.62 で残していた自然な無限根作用と実テンソル上の pd 構造・普遍性の接続は本工程で解消した。
A 上の φ_A 引戻し全体との同定、原典の R/ϖ 表記との最終照合、prism 商の p 正則性仮定の解消、
絶対 prismatic envelope の同定は引き続き未完了。条件付きの実 pd 普遍性だけで全体の完成と数えない。
承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 4 ファイルの対象ビルドと集約ビルドは終了コード 0
（最終保存版 4540 jobs）。新規 24 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6229 宣言の推移的公理依存は標準 3 公理のみ。
新規 24 公開宣言の正確な型を `#check` で確認した（終了コード 0）。
原典とは異なる経路を docstring にも明記した。


### E1.64 A 全体の実 Frobenius 引戻しと自然な入力環上の pd 普遍性（2026-10-17）

前工程 E1.63 は検証済みコードをコミットした進捗。外部依存の破損はない。
本工程は商環 R/ϖ → R/p に沿うテンソル比較から、A 全体の φ_A 引戻しへ進む。

E1.63 と同じ完全 prism W : OrientedPrism p A、hW、f : Polynomial A と、
実 Hodge–Tate 候補 T、自然な基底射 φ : R →+* T、R=A/W.ideal、
Rv=R/ϖ、Rp=R/p、Mv=T/(Ideal.map φ (ϖ))、Np、zp、Dp を使う。
φ_A は `DeltaStructure.frobeniusEquiv W.deltaStructure hW`。
bv : A →+* Rv、bp : A →+* Rp は元の二段商射。
左の A は同じ宇宙の環の写し Ac=`TensorBaseCopy A` で区別する。
ι : A ≃+* Ac は値を包む同型で、左への A 作用は αc=ι∘φ_A による作用。
qA : A →+* Mv は自然な Rv 作用と bv の合成である。
At=Ac ⊗[A] Mv は qA.toAlgebra と αc.toRingHom.toAlgebra を使う。
比較先 Dp の Ac 作用は Ac→A→Rp→Dp の元の係数作用とする。

新規 `Andre/AutomorphismTensorPullback.lean` に 6 公開宣言を追加した。
`TensorBaseCopy` は一つの値を包む型の写し、`tensorBaseCopyEquiv` は値の全単射、
`tensorBaseCopyCommRing` と `tensorBaseCopyRingEquiv` は移送した可換環と値の環同型。
全て宇宙を上げない。
`automorphismTensorPullbackAlgEquiv` は任意宇宙の可換環 A、B、C、自己同型 α、
q : A →+* B、r : A →+* C、F : B ≃+* C、
hF : ∀ a, F (q a) = r (α a) に対し、

```lean
let := q.toAlgebra
let := (r.comp (tensorBaseCopyRingEquiv A).toRingHom).toAlgebra
let := (α.trans (tensorBaseCopyRingEquiv A).symm).toRingHom.toAlgebra
TensorBaseCopy A ⊗[A] B ≃ₐ[TensorBaseCopy A] C
```

を構成する。同 `_tmul` は、値 a の写しと b の単純テンソルを r a * F b へ送る。
正則性・平坦性・商に関する仮定はない。

新規 `Andre/PowerRootPrismMonicFullFrobeniusPullback.lean` に 6 公開宣言を追加した。
`powerRootPrismMonicVarpiBaseMap` は qA を定義し、同 `_coeff` は

```lean
qA a = powerRootPrismMonicVarpiInputMap W hW f (algebraMap A P a)
```

を証明する。元の実完備化単位・商射と無限根入力射の自然な A 作用そのもの。
`powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff` は hf : f.Monic の下で、
既存の実剰余比較 U について

```lean
U (qA a) = algebraMap Rp Dp (bp (φ_A a))
```

を証明する。
`powerRootPrismMonicFullFrobeniusPullbackAlgEquiv` は同じ hf のみから
上記の四つの環・代数構造を let で指定した後の `At ≃ₐ[Ac] Dp` を与える。
同 `_tmul` と同 `_variable` の結論はそれぞれ

```lean
E ((⟨a⟩ : Ac) ⊗ₜ[A] m) = algebraMap Rp Dp (bp a) * U m
E ((1 : Ac) ⊗ₜ[A] ψ (powerRootPolynomialVariable A p hp (n + 1))) =
  algebraMap Np Dp (powerRootPolynomialVariable Rp p hp n)
```

である。ψ は元の自然な無限根入力射。p 正則性・正次数は仮定しない。

新規 `Andre/PowerRootPrismMonicFullFrobeniusPD.lean` に 10 公開宣言を追加した。
`powerRootPrismMonicFullFrobeniusInputAlgebra` は E⁻¹ に沿う Np 作用を At に与え、
`powerRootPrismMonicFullFrobeniusInputAlgEquiv` は同じ環同型を `At ≃ₐ[Np] Dp` に強める。
同 `_InputAlgebra_base_coeff` と同 `_InputAlgebra_variable` は

```lean
algebraMap Np At (algebraMap Rp Np (bp a)) = algebraMap Ac At (⟨a⟩ : Ac)
algebraMap Np At (powerRootPolynomialVariable Rp p hp n) =
  (1 : Ac) ⊗ₜ[A] ψ (powerRootPolynomialVariable A p hp (n + 1))
```

を証明する。従って入力環作用は元の係数と元の自然な根変数を保持する。
これらの作用の自然性と入力像のイデアル所属は hf のみを前提とする。

E_N : At ≃ₐ[Np] Dp とし、J は標準正次数イデアルを E_N⁻¹ で写した At のイデアル。
`powerRootPrismMonicFullFrobeniusPDIdeal` は J を定義する。
`powerRootPrismMonicFullFrobeniusDividedPowers` は hf に加えて
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)` の下で `DividedPowers J` を構成する。
同 `_InputAlgEquiv_isDPMorphism` は E_N の実分冪射性、同 `_DividedPowers_input_apply` は
全 n : ℕ に対して入力像の n 次分冪が E_N⁻¹ (principalDPGenerator zp n) であることを証明する。
`existsUnique_powerRootPrismMonicFullFrobeniusPDMorphism` は W、hW、f、hf、hpR、
任意宇宙の可換環 B、Algebra Np B、I : Ideal B、Ht : DividedPowers I、
hzB : algebraMap Np B zp ∈ I の下で、実環構造・四つの代数作用を let で導入した後の

```lean
∃! F : At →ₐ[Np] B,
  (powerRootPrismMonicFullFrobeniusDividedPowers W hW f hf hpR).IsDPMorphism
    Ht F.toRingHom
```

を証明する。標的のねじれ・完備性・非零性は仮定しない。正次数も不要。
BS Rem 7.15(1)（著者版 p.62）に対する原典とは異なる、型の写し・半線形環同型・
通常テンソル・実分冪構造の移送による経路であることを docstring に明記した。

これで元の自然な A 作用に沿う A 全体の φ_A 引戻しと、元の mod p 入力の実 pd 普遍性を
接続した。原典の R/ϖ 表記と今回の R/p 係数作用の最終照合、prism 商の p 正則性仮定の解消、
絶対 prismatic envelope との同定は引き続き未完了。係数環を暗黙に同一視せず、条件付きの
実 pd 比較だけで全体の完成と数えない。承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 3 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4543 jobs）。新規 22 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6485 宣言の推移的公理依存は標準 3 公理のみ。
新規 22 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.65 射影的な正次数商によるモニック実 pd 比較の p 正則性仮定の解消（2026-10-17）

前工程 E1.64 は検証済みコードをコミットした進捗。本工程は pd 構造・pd 普遍性に残っていた
`hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)` を解消する。
この仮定は旧 `perfectPrismVarpiLift_modPrime_regular` と正則係数元による分冪降下で使われていた。
モニック入力の正次数商は係数環上自由なので、商射の線形切断を使えば係数元の正則性は不要。
以下では原典とは異なる射影性による切断の経路を採る。

新規 `Andre/DividedPowerProjectiveCoefficientQuotient.lean` に 5 公開宣言を追加した。
可換環 R、R 代数 D、J : Ideal D と `[Module.Projective R (D ⧸ J)]` を固定する。
`exists_coefficient_mul_representative_of_projective_quotient` の正確な型は

```lean
(a : R) (b : D) (hb : algebraMap R D a * b ∈ J) :
  ∃ c ∈ J, algebraMap R D a * c = algebraMap R D a * b
```

である。商射 q : D →ₗ[R] D/J の線形切断 s を取り c=b−s(q b) とする。
q(a b)=0 と s の R 線形性から a c=a b、q c=0 から c∈J を示す。
D 自身の R 上の平坦性も係数元 a の正則性も要求しない。
`dividedPower_coefficient_span_inf_isSubDPIdeal_of_projective` は
H : DividedPowers J、a : R の下で

```lean
H.IsSubDPIdeal (Ideal.span {algebraMap R D a} ⊓ J)
```

を証明する。上記の代表元で γ_n(a c)=a^n γ_n(c) を適用する。
`dividedPowersQuotientOfProjectiveCoefficient` の結論は

```lean
DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D a})))
```

であり、同 `_apply` は任意の n と x∈J に対し分冪値が H.dpow n x の商像と一致すること、
同 `_isDPMorphism` は標準商射の分冪射性を証明する。

新規 `Andre/PowerRootCoefficientPDProjectiveReduction.lean` に 3 公開宣言を追加した。
完全 prism W、hW、f : Polynomial A、hf : f.Monic を固定し、
R₀=A/(p)、N=PowerRootPolynomial R₀ p hp、z=powerRootCoefficientPDInput p f、
D=PowerRootCoefficientPDEnvelope p f、J=principalDPPositiveIdeal z とする。
`powerRootCoefficientPDReductionOfMonic` は任意の a : R₀ に対して

```lean
DividedPowers (J.map (Ideal.Quotient.mk (Ideal.span {algebraMap R₀ D a})))
```

を構成する。既存 `powerRootCoefficientPDPositiveQuotient_free p f hf` から射影性を供給する。
同 `_base_apply` は入力係数像の n 次分冪が n 次標準分冪生成元の商像になること、
同 `_isDPMorphism` は実係数商射の分冪射性を証明する。a の正則性は不要。

新規 `Andre/MonicPerfectPrismPDEnvelope.lean` に 6 公開宣言を追加した。
Rv=(A/W.ideal)/ϖ、Nv=PowerRootPolynomial Rv p hp、bv : A →+* Rv は二段商射、
zv=powerRootPolynomialBaseMap Rv p hp (f.map bv)、Dv=PrincipalDPPresentation Nv zv とする。
`perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf` は
`DividedPowers (principalDPPositiveIdeal zv)` を、上記の任意係数還元で
ϖ の持上げの mod p 像を選び、既存の実台環比較で移送して構成する。
同 `_base_apply` は入力像の全分冪値を標準生成元と同定する。
`existsUnique_perfectPrismVarpiNativePDMorphismOfMonic` は任意宇宙の可換環 B、
Algebra Nv B、I : Ideal B、Ht : DividedPowers I、hzB : algebraMap Nv B zv ∈ I に対し

```lean
∃! F : Dv →ₐ[Nv] B,
  (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf).IsDPMorphism Ht F.toRingHom
```

を証明する。prism 商の p 正則性、入力の正次数、標的のねじれ・完備性は仮定しない。

さらに Rp=(A/W.ideal)/p、Np=PowerRootPolynomial Rp p hp、bp : A →+* Rp は二段商射、
zp=powerRootPolynomialBaseMap Rp p hp (f.map bp)、Dp=PrincipalDPPresentation Np zp とする。
`powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf` は同じ仮定だけで
`DividedPowers (principalDPPositiveIdeal zp)` を構成する。
逆 Frobenius 係数入力を Rv 側に使い、指定係数 Frobenius 同型で元の f の mod p 入力へ戻す。
同 `_base_apply` は標準分冪値の公式、`existsUnique_powerRootPrimeFrobeniusPDMorphismOfMonic` は
任意の Np 代数分冪標的に対する `∃! F : Dp →ₐ[Np] B, Hs.IsDPMorphism Ht F.toRingHom` を証明する。
ここでも hpR と正次数は不要。

新規 `Andre/PowerRootPrismMonicFullFrobeniusPDOfMonic.lean` に 4 公開宣言を追加した。
At=TensorBaseCopy A ⊗[A] Mv とその元の A 作用・左 Frobenius 作用・自然な Np 作用、
E_N : At ≃ₐ[Np] Dp、実イデアル Jt は E1.64 と同一のものを使う。
`powerRootPrismMonicFullFrobeniusDividedPowersOfMonic W hW f hf` は、
実環構造・四つの代数作用を let で指定した後の `DividedPowers Jt` を構成する。
`powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphismOfMonic` は E_N の実分冪射性、
`powerRootPrismMonicFullFrobeniusDividedPowersOfMonic_input_apply` は全標準分冪値を証明する。
`existsUnique_powerRootPrismMonicFullFrobeniusPDMorphismOfMonic` の引数は
W、hW、f、hf、任意宇宙の可換環 B、Algebra Np B、I : Ideal B、Ht : DividedPowers I、
hzB : algebraMap Np B zp ∈ I で、正確な結論は必要な let の後の

```lean
∃! F : At →ₐ[Np] B,
  (powerRootPrismMonicFullFrobeniusDividedPowersOfMonic W hW f hf).IsDPMorphism
    Ht F.toRingHom
```

である。旧定理の hpR を残した条件付き普遍性とは異なり、この pd 比較に hpR は残らない。
BS Rem 7.15(1)（著者版 p.62）に対する原典とは異なる、自由性からの線形切断・
半線形比較・通常テンソル・実分冪構造の移送による証明である旨を docstring と本記録に明記した。

これにより Rv 側、元の mod p 入力側、A 全体の実 Frobenius 引戻し側の pd 構造と普遍性から
prism 商の p 正則性仮定を解消した。raw 除算包・その実完備化の正則性と完全忠実平坦性に
残る hpR まで解消したとは主張しない。原典の R/ϖ 表記と今回の R/p 係数作用の最終照合、
絶対 prismatic envelope との同定も引き続き未完了。承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 4 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4547 jobs）。新規 18 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6732 宣言の推移的公理依存は標準 3 公理のみ。
新規 18 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.66 互換な根データからの無限根入力 δ 射と実完備化の一意普遍射（2026-10-17）

前工程 E1.65 は pd 構造と普遍性から p 正則性を除き、検証済みコードをコミットした進捗。
本工程は絶対 prismatic envelope との比較で残る、指定無限根入力 δ 射の構成へ進む。
既存の相対普遍性は g : P →+* B 自体を入力としていたので、互換根列からその g を
実際に構成し、係数・全根変数を保つ普遍性まで証明する。

新規 `Andre/PowerRootExponentEvaluation.lean` に 6 公開宣言を追加した。
任意宇宙の可換モノイド B、p : ℕ、hp : 0 < p、ρ : ℕ → B、
hρ : ∀ n, ρ (n+1)^p=ρ n を固定する。
`compatiblePowerRoots_iterate` は `ρ (n+m)^(p^m)=ρ n`、
`compatiblePowerRoots_repr_eq` は有理指数 k/p^n=l/p^m なら `ρ n^k=ρ m^l` を証明する。
`powerRootExponentEval` は分母表示を選んで指数 q を根列の冪へ評価し、
同 `_of_repr` は q*p^n=k の任意表示でその値が ρ n^k になることを示す。
`powerRootExponentEvalHom` は

```lean
Multiplicative (powerRootExponentMonoid p hp) →* B
```

を構成する。零指数を単位へ送り、共通分母の段へ揃えて加法を乗法へ送る。
同 `_variable` は第 n 根変数の指数の像が ρ n であることを証明する。
素数性・標数・非零性・根の単射性を仮定しない。

新規 `Andre/PowerRootPolynomialUniversal.lean` に 5 公開宣言を追加した。
任意宇宙の可換環 R と B、p、hp、係数射 f : R →+* B と上記の根列を固定する。
P=PowerRootPolynomial R p hp とする。
`powerRootPolynomial_ringHom_ext` は二つの環射が係数と全根変数上で一致すれば等しいと示す。
各単項式をある有限段の変数の冪に表して証明する。
`powerRootPolynomialEval` は指数モノイド射と係数射を加法モノイド環の普遍射で延長した実環射。
同 `_coeff`、同 `_variable` は係数と各根の指定値を証明する。
`existsUnique_powerRootPolynomialHom` の正確な型は

```lean
∃! F : P →+* B,
  F.comp (algebraMap R P) = f ∧
    ∀ n, F (powerRootPolynomialVariable R p hp n) = ρ n
```

である。通常の任意の可換環を標的とし、完備性・prism・正則性を要求しない。

新規 `Andre/PowerRootPolynomialDeltaUniversal.lean` に 5 公開宣言を追加した。
p を素数、hp をその正値性とする。
`isDeltaHom_powerRootPolynomial` は任意の源 δ 構造 D_P と終域 δ 構造 E、環射 g について、
係数・全根変数上の δ 互換性から `D_P.IsDeltaHom E g` を証明する。
二つの W₂ 切断の合成を外延性で比較するため、終域の p ねじれも許す。
`compatiblePowerRoots_delta_eq_zero` は `[IsHausdorff (Ideal.span {(p:B)}) B]` の下で
根列の全元の δ が零であることを、既存の全 p 冪根による rank 1 判定から導く。

R には hpR : Function.Injective (fun a:R => (p:R)*a)、D : DeltaStructure p R を与える。
E : DeltaStructure p B、係数射 f、hf : D.IsDeltaHom E f と、ρ、hρ、
hδρ : ∀ n, E.delta (ρ n)=0 の下で `powerRootPolynomialEval_isDeltaHom` は
実評価射が `powerRootPolynomialDelta p hpR D` から E への δ 射であることを証明する。
`existsUnique_powerRootPolynomialDeltaHom` は

```lean
∃! g : P →+* B,
  (powerRootPolynomialDelta p hpR D).IsDeltaHom E g ∧
    g.comp (algebraMap R P) = f ∧
      ∀ n, g (powerRootPolynomialVariable R p hp n) = ρ n
```

を証明する。終域の p 正則性・完全性・完備性は仮定しない。
`existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff` は終域の p 進分離性から
hδρ を自動で供給し、同じ結論を hδρ を引数にせず証明する。

新規 `Andre/PowerRootPrismMonicRootUniversal.lean` に 3 公開宣言を追加した。
`powerRootPolynomialEval_baseMap` は任意の通常多項式 f について

```lean
powerRootPolynomialEval p hp k ρ hρ (powerRootPolynomialBaseMap R p hp f) = f.eval₂ k (ρ 0)
```

を証明する。モニック性は不要。

完全 prism W : OrientedPrism p A、hW、f : Polynomial A を固定する。
P、E、dP、a、L、jL、H、uL、DH は既存の同じ無限根 raw 実完備化のもの。
`existsUnique_powerRootPrismMonicCompletionHom_of_roots` は同じ宇宙の可換環 B、
Q : OrientedPrism p B、k : A →+* B、hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k、
hd : k W.generator=Q.generator、ρ : ℕ → B、hρ : ∀ n, ρ(n+1)^p=ρ n、
hδρ : ∀ n, Q.deltaStructure.delta (ρ n)=0、hroot : Q.generator ∣ f.eval₂ k (ρ 0) の下で、
実環構造を let で導入した後の

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
      ∀ n, F (uL (jL (powerRootPolynomialVariable A p hp n))) = ρ n
```

を証明する。g 自体を前提に残さず、上記の具体的評価で構成する。
この普遍射の構成には f のモニック性・正次数、源の prism 商の p 正則性は不要。
源 H 自体が prism であることをここで追加主張するものではない。
`existsUnique_powerRootPrismMonicCompletionHom_of_p_regular_roots` は
hpB : Function.Injective (fun x:B => (p:B)*x) を持つ試験 prism Q に対し、
Q の導来 p 完備性から分離性を得て hδρ を自動で供給し、同じ結論を証明する。
p 正則性を課すのは試験 prism の台環 B であり、源の prism 商ではない。

BS Rem 7.15（著者版 p.62）に対する原典とは異なる、有理指数の表示独立性・
モノイド環の普遍射・W₂ 切断・実完備化による経路を docstring に明記した。
絶対 envelope との比較に残るのは、剰余上の根列を試験 prism の台環内の互換根列へ
一意に持ち上げることと、一般の基底 prism 射の生成元の単元係数を扱うこと。
ここで与えている根列は B 内の実根列であり、B/Q.ideal 内の根列からの持上げを証明したとは数えない。
raw・実完備化の正則性と完全忠実平坦性に残る hpR、原典の係数表記との照合も未完了。
承認済み hdeg を持つ任意族存在定理の型は変更していない。
原典の S=R⟨Y^{1/p^∞}⟩/(f) の完備化とこの未完備入力環との接続も、絶対比較の未完了範囲に含む。

検証：新規 4 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4551 jobs）。新規 19 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6811 宣言の推移的公理依存は標準 3 公理のみ。
新規 19 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.67 共通完備商による剰余根列の一意持上げと完全試験 prism への普遍性（2026-10-17）

前工程 E1.66 は実根列からの入力 δ 射と実完備化の一意普遍射を検証・保存した進捗。
本工程では根列を試験 prism の商に指定する形へ進めた。
Witt 表示で各根を選び直す経路ではなく、Perfection の共通完備商の同型を用いる。

新規 `Andre/CommonAdicCompatibleRoots.lean` に 5 公開宣言を追加した。
`perfectionCongrMulEquiv` は任意の自然数 p、任意宇宙の可換モノイド M、N、同型 e : M ≃* N に対し
`Perfection M p ≃* Perfection N p` を全座標への e と e⁻¹ の作用として与える。
素数性・環構造は不要。

可換環 B、素数 p、I J : Ideal B、hJI : J≤I を固定する。
`[CharP (B ⧸ I) p]`、`[IsAdicComplete I B]` と
`[IsAdicComplete (I.map (Ideal.Quotient.mk J)) (B ⧸ J)]` の下で、
`perfectionQuotientEquivOfCommonAdic` は

```lean
Perfection B p ≃* Perfection (B ⧸ J) p
```

を構成する。二つの既存の完備商 Teichmüller 同型と第三同型定理で比較し、
順射は元の商射を全座標へ作用させるものとする。
同 `_coeff` は全 x : Perfection B p、n : ℕ に対し

```lean
Perfection.coeffMonoidHom (B ⧸ J) p n (E x) =
  Ideal.Quotient.mk J (Perfection.coeffMonoidHom B p n x)
```

を証明する。
`existsUnique_compatiblePowerRootsLift_of_common_adic` は上記の仮定と
ρ : ℕ → B ⧸ J、hρ : ∀ n, ρ(n+1)^p=ρ n の下で

```lean
∃! σ : ℕ → B,
  (∀ n, σ (n+1)^p = σ n) ∧ ∀ n, Ideal.Quotient.mk J (σ n) = ρ n
```

を証明する。列全体を同時に持ち上げるため、個々の根の任意選択には依存しない。

`existsUnique_compatiblePowerRootsLift_of_adic_ideals` は標数インスタンスの仮定を除き、
代わりに hpI : (p:B)∈I を使い、同じ結論を零環も含めて証明する。
共通商 B/I が非零なら標数 p を供給し、零なら I=⊤ と I 完備性から B も零と示す。
この一般結果は δ 構造・p 正則性・prism・非零性を仮定しない。

新規 `Andre/PerfectPrismPairAdicComplete.lean` に 2 公開宣言を追加した。
Q : OrientedPrism p B と hQ : Q.deltaStructure.IsPerfect を固定する。
`perfectPrism_generator_power_quotient_prime_complete` は全 n : ℕ に対し

```lean
IsAdicComplete (Ideal.span {(p : B)}) (B ⧸ (Ideal.span {Q.generator}) ^ n)
```

を証明する。distinguished 冪商の p 完備性を元の B 作用へ戻す。
`perfectPrism_pair_isAdicComplete` は d 完備性と全 d 冪商の p 完備性から

```lean
IsAdicComplete (Ideal.span {(p : B), Q.generator}) B
```

を証明する。商の p 正則性や p,d の正則列条件を使わない。

新規 `Andre/PerfectPrismCompatibleRootsLift.lean` に 2 公開宣言を追加した。
`prism_pair_map_ideal_eq_prime` は完全性を使わず、(p,d) の Q.ideal 商での像が p 主イデアルと示す。
`existsUnique_perfectPrismCompatibleRootsLift Q hQ ρ hρ` は上記の二つの完備性と
完全 prism 商の p 完備性を共通完備商の一般結果へ渡し、

```lean
∃! σ : ℕ → B,
  (∀ n, σ(n+1)^p=σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n)=ρ n
```

を証明する。ρ は B/Q.ideal 内の根列であり、B 内への持上げ自体を引数にしない。
零環と p ねじれを持つ prism 商を含む。試験 prism の完全性は明示前提。

新規 `Andre/PowerRootPolynomialPrismLift.lean` に 1 公開宣言を追加した。
源 R の p 正則性 hpR、D : DeltaStructure p R、完全試験 prism Q、hQ、
k : R →+* B、hk : D.IsDeltaHom Q.deltaStructure k、商内の根列 ρ、hρ の下で、
`existsUnique_powerRootPolynomialDeltaHom_of_perfectPrism_residue_roots` は
P=PowerRootPolynomial R p hp として

```lean
∃! g : P →+* B,
  (powerRootPolynomialDelta p hpR D).IsDeltaHom Q.deltaStructure g ∧
    g.comp (algebraMap R P)=k ∧
      ∀ n, Ideal.Quotient.mk Q.ideal (g (powerRootPolynomialVariable R p hp n))=ρ n
```

を証明する。源の完全性は不要で、R と B の宇宙は独立。
一意に持ち上げた実根列の rank 1 性を p 進分離性から供給する。
台環内の根列と δ=0 の条件を引数に残さない。

新規 `Andre/PowerRootPrismMonicResidueRootUniversal.lean` に 1 公開宣言を追加した。
完全な源 prism W、hW、f : Polynomial A と既存の P、E、dP、a、L、jL、H、uL、DH を使う。
`existsUnique_powerRootPrismMonicCompletionHom_of_perfect_residue_roots` は
同じ宇宙の試験環 B、完全 prism Q、hQ、基底 δ 射 k、hk、
hd : k W.generator=Q.generator、ρ : ℕ → B/Q.ideal、hρ と

```lean
hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k) (ρ 0)=0
```

の下で、元の H の環構造を let で導入した後の

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f)=k ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n))))=ρ n
```

を証明する。指定入力 δ 射 g、実根列 σ、その rank 1 条件は前提に残らない。
源の prism 商の p 正則性、f のモニック性・正次数もこの普遍射には不要。
源 H 自体の prism 性を追加主張するものではない。

BS Rem 7.15（著者版 p.62）に対する原典とは異なる、共通完備商・Teichmüller モノイド同型・
有理指数評価・W₂ 切断・実完備化による経路を docstring と本記録に明記した。
完全試験 prism では剰余根列の一意持上げを解消したが、一般の試験 prism についての
共通完備性の供給、一般の基底 prism 射の生成元の単元係数、原典の完備入力環 S との接続は未完了。
raw 包・実完備化の正則性と完全忠実平坦性に残る hpR、原典の係数表記との照合も残る。
完全試験環に対する普遍性を絶対 prismatic envelope 全体の同定と数えない。
承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 5 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4557 jobs）。新規 11 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6880 宣言の推移的公理依存は標準 3 公理のみ。
新規 11 公開宣言の正確な型を `#check` で確認した（終了コード 0）。


### E1.68 一般有界試験 prism の根列持上げと入力 δ 射の普遍性（2026-10-17）

前工程 E1.67 は完全試験 prism に対する剰余根列の一意持上げを検証・保存した進捗。
本工程は試験 prism の完全性を外し、その商の p 冪ねじれの有界性から共通完備性を証明する。

新規 `Andre/RegularPowerQuotientTorsion.lean` に 2 公開宣言を追加した。
任意の可換環 B、a d : B、hd : Function.Injective (fun x:B => d*x)、N : ℕ を固定する。
`regular_power_quotient_torsion_bound_dvd` は

```lean
hN : ∀ k : ℕ, ∀ x : B, d ∣ a^k*x → d ∣ a^N*x
m k : ℕ
x : B
hx : d^m ∣ a^k*x
⊢ d^m ∣ a^(N*m)*x
```

を証明する。a^N*x=d*y と書き、d の正則性で y を一段低い冪商へ帰着する。
`regular_power_quotient_torsion_bound` は同じ内容を実商環で述べる。
B/(d) の a 冪ねじれが a^N で消えるとき、全 m,k と x : B/(d^m) に対し

```lean
(qa)^k*x=0 → (qa)^(N*m)*x=0
```

を証明する。qa は a の該当商への標準像。a の正則性・素数性・δ 構造は不要で、
零冪商・N=0 を含む。これは原典とは異なる可除性による帰納計算である。

以下、Q : OrientedPrism p B の商の有界性を、正確に

```lean
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0
```

とする。試験 prism の完全性、台環や商の p 正則性、非零性は仮定しない。

新規 `Andre/BoundedPrismAdicComplete.lean` に 4 公開宣言を追加した。
`boundedPrism_generator_power_quotient_prime_complete Q hB m` は

```lean
IsAdicComplete (Ideal.span {(p:B)}) (B ⧸ (Ideal.span {Q.generator})^m)
```

を証明する。一乗商の有界指数 N を N*m へ移し、Q.complete_p からの商の導来完備性と
既存の有界ねじれ比較を使う。源 B 自体の古典的 p 完備性を仮定していない。
`boundedPrism_pair_isAdicComplete Q hB` は d 完備性と全冪商の p 完備性から

```lean
IsAdicComplete (Ideal.span {(p:B), Q.generator}) B
```

を構成する。
`boundedPrism_quotient_isAdicComplete_prime Q hB` は

```lean
IsAdicComplete (Ideal.span {(p:B ⧸ Q.ideal)}) (B ⧸ Q.ideal)
```

を商の導来 p 完備性と hB から証明する。
`boundedPrism_isHausdorff_prime Q hB` は (p)⊆(p,d) の冪合同を使い、
`IsHausdorff (Ideal.span {(p:B)}) B` を証明する。
これにより全実根の rank 1 判定に必要な p 進分離性も供給できる。

新規 `Andre/BoundedPrismCompatibleRootsLift.lean` に 1 公開宣言を追加した。
`existsUnique_boundedPrismCompatibleRootsLift Q hB ρ hρ` は
ρ : ℕ → B/Q.ideal、hρ : ∀ n, ρ(n+1)^p=ρ n の下で

```lean
∃! σ : ℕ → B,
  (∀ n, σ(n+1)^p=σ n) ∧ ∀ n, Ideal.Quotient.mk Q.ideal (σ n)=ρ n
```

を証明する。(p,d) の Q.ideal 商での像が (p) である計算と、上記の二つの完備性を
共通完備商の一般の根列持上げに供給する。零環と p ねじれを持つ台環・商を含む。
完全試験 prism に限定していた根列の持上げは、一般有界試験 prism へ拡張した。

新規 `Andre/PowerRootPolynomialBoundedPrismLift.lean` に 1 公開宣言を追加した。
源 R の p 正則性 hpR、D : DeltaStructure p R、Q、hB、
k : R →+* B、hk : D.IsDeltaHom Q.deltaStructure k、ρ、hρ に対し、
P=PowerRootPolynomial R p hp として
`existsUnique_powerRootPolynomialDeltaHom_of_boundedPrism_residue_roots` は

```lean
∃! g : P →+* B,
  (powerRootPolynomialDelta p hpR D).IsDeltaHom Q.deltaStructure g ∧
    g.comp (algebraMap R P)=k ∧
      ∀ n, Ideal.Quotient.mk Q.ideal (g (powerRootPolynomialVariable R p hp n))=ρ n
```

を証明する。源と標的の宇宙は独立で、源の完全性は不要。
実根列を一意に持ち上げ、p 進分離性から δ=0 を供給する。
試験 prism の完全性を追加仮定に残さない。

新規 `Andre/PowerRootPrismMonicBoundedResidueRootUniversal.lean` に 1 公開宣言を追加した。
完全な源 prism W、hW、f : Polynomial A と、既存の P、E、dP、a、L、jL、H、uL、DH を使う。
`existsUnique_powerRootPrismMonicCompletionHom_of_bounded_residue_roots` は同じ宇宙の Q、hB、
基底 δ 射 k、hk、hd : k W.generator=Q.generator、ρ、hρ、
hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k) (ρ 0)=0 の下で、
元の H の環構造を let で導入した後の

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f)=k ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n))))=ρ n
```

を証明する。実根列・指定入力 δ 射・試験 prism の完全性や p 正則性は前提に残らない。
源の prism 商の p 正則性、f のモニック性・正次数もこの普遍射には不要。

BS Rem 7.15（著者版 p.62）に対する原典とは異なる、主イデアルの可除性帰納・
有界ねじれ比較・共通完備商・Perfection のモノイド同型・W₂ 切断の経路を docstring に明記した。
これで一般有界試験 prism に対する根列の持上げと入力射の一意性を解消したが、
生成元の単元係数を持つ一般の基底 prism 射、原典の完備入力環 S との接続、
源 H 自体の prism 性・raw と実完備化の正則性と完全忠実平坦性に残る hpR は未完了。
原典の係数表記との最終照合も残る。絶対 prismatic envelope 全体の同定とはまだ数えない。
承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 5 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4562 jobs）。新規 9 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6938 宣言の推移的公理依存は標準 3 公理のみ。
新規 9 公開宣言の正確な型を `#check` で確認した（終了コード 0）。

### E1.69 一般の基底 prism 射に対する実完備化の普遍性（2026-10-17）

本節は André E1・E2 の追記。E1.68 の基底生成元の厳密な一致条件を解消した。
新規 `Andre/BoundedPrismHomRigidity.lean` に 5 公開定理を追加した。
共通の型と仮定は次の通り（源・標的の宇宙は独立）。

```lean
{p : ℕ} [Fact p.Prime]
{A : Type u} {B : Type v} [CommRing A] [CommRing B]
{P : OrientedPrism p A} {Q : OrientedPrism p B}
(F : OrientedPrism.Hom P Q)
(hP : P.deltaStructure.IsDistinguished P.generator)
(hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0)
```

これらの引数の下で、各定理の結論は正確に以下。

```lean
-- existsUnique_boundedPrismHom_generator_unit
∃! z : Bˣ, F.toRingHom P.generator = Q.generator * z
-- boundedPrismHom_generator_span
Ideal.span {F.toRingHom P.generator} = Q.ideal
-- boundedPrismHom_generator_regular
Function.Injective (fun x : B => F.toRingHom P.generator * x)
-- boundedPrismHom_generator_complete
IsModuleComplete B (F.toRingHom P.generator) (ModuleCat.of B B)
-- boundedPrismHom_map_ideal_eq
P.ideal.map F.toRingHom = Q.ideal
```

像の distinguished 性と標的の (p,d) 古典的完備性から、生成元の像の係数が単元であることを示す。
一意性には標的生成元の正則性を使う。標的の完全性・p 正則性は不要。
源も完全性までは要求せず、指定生成元の distinguished 性だけを引数にする。

新規 `Andre/PowerRootPrismMonicBasePrismUniversal.lean` に 1 公開定理を追加した。
完全な源 prism W、hW、f : Polynomial A に対し、P、E、dP、a、L、jL、H、uL、DH は
E1.68 と同じ実際の環・写像・δ 構造を指す。
`existsUnique_powerRootPrismMonicCompletionHom_over_bounded_prism` の引数は、
同じ宇宙の B、Q、上記 hB、一般の基底 prism 射 k : OrientedPrism.Hom W Q、
ρ : ℕ → B ⧸ Q.ideal、hρ : ∀ n, ρ (n+1)^p=ρ n、
hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k.toRingHom) (ρ 0)=0。
元の H の環構造 `pdCompletionCommRing L p (jL dP)` を let で導入した後の結論は

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f)=k.toRingHom ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n))))=ρ n
```

である。`k.toRingHom W.generator=Q.generator` は仮定しない。
一意な入力 δ 射の生成元の像について、新しい補題で可除性・正則性・完備性を供給し、
既存の raw 実完備化の普遍性を適用する。source の prism 商の p 正則性、
f のモニック性・正次数はこの普遍射の前提ではない。

BS Rem 7.15（著者版 p.62）への応用であり、原典とは異なる有界ねじれ・
共通古典的完備性・生成元の単元係数による経路であることを docstring に明記した。
原典の完備入力環 S との接続、源 H 自体の prism 性、raw と実完備化の正則性・
完全忠実平坦性に残る hpR、原典の係数表記との最終照合は未完了。
一般基底射に対する普遍射は証明したが、絶対 prismatic envelope 全体の同定とは数えない。
承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 2 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4564 jobs）。新規 6 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 6987 宣言の推移的公理依存は標準 3 公理のみ。
新規 6 公開宣言の正確な型を `#check` で確認した（終了コード 0）。
