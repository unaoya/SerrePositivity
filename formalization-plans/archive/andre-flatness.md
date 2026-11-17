# André の平坦性補題の引用解消

> **アーカイブ（2026-10-18）**：André の平坦性補題（BS Thm 7.14）は証明済み。数学は解説の `par:bs-andre`・`par:bs-andre-envelope` と `BhattScholze/Inputs/AndreFlatness.lean` の docstring、経路の差は [BS 主計画](../bhatt-scholze/notes/bhatt-scholze.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


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

### E1.70 通常の方程式商の普遍性と実完備化への入力（2026-10-17）

本節は André E1・E2 の追記。E1.69 の剰余根列による試験データを、
通常の方程式商からの実際の環射に置き換える工程。
新規 `Andre/PowerRootEquationQuotient.lean` に 7 公開宣言を追加した。
共通の引数は {R : Type u} [CommRing R]、p : ℕ、hp : 0 < p、f : Polynomial R。
P=PowerRootPolynomial R p hp、I=Ideal.span {powerRootPolynomialBaseMap R p hp f} とする。
以下は定義または定理の正確な型・結論（B の宇宙 v は u と独立）。

```lean
PowerRootEquationQuotient p hp f : Type u := P ⧸ I
powerRootEquationQuotientCoeff p hp f : R →+* PowerRootEquationQuotient p hp f
powerRootEquationQuotientRoot p hp f (n : ℕ) : PowerRootEquationQuotient p hp f
-- powerRootEquationQuotientRoot_pow p hp f n
powerRootEquationQuotientRoot p hp f (n+1)^p = powerRootEquationQuotientRoot p hp f n
-- powerRootEquationQuotientRoot_equation p hp f
f.eval₂ (powerRootEquationQuotientCoeff p hp f)
  (powerRootEquationQuotientRoot p hp f 0) = 0
```

c=powerRootEquationQuotientCoeff p hp f、r=powerRootEquationQuotientRoot p hp f、
S=PowerRootEquationQuotient p hp f と書くと、
`powerRootEquationQuotient_ringHom_ext` は {B : Type v} [CommRing B]、
F G : S →+* B、hc : F.comp c=G.comp c、hr : ∀ n, F (r n)=G (r n) の下で F=G を証明する。
`existsUnique_powerRootEquationQuotientHom` は、同じ B、k : R →+* B、
ρ : ℕ → B、hρ : ∀ n, ρ (n+1)^p=ρ n、hf : f.eval₂ k (ρ 0)=0 の下で

```lean
∃! F : S →+* B, F.comp c=k ∧ ∀ n, F (r n)=ρ n
```

を証明する。モニック性・正次数・素数性は前提ではなく、零環や定数多項式も含む。
無限根多項式の具体的評価を主イデアルで降下し、係数と全根による外延性で一意性を示す。

新規 `Andre/PowerRootPrismMonicEquationInput.lean` に 1 公開定理を追加した。
完全な源 prism W : OrientedPrism p A、hW、f : Polynomial A、p の素数性を固定する。
P、E、dP、a、L、jL、H、uL、DH は E1.69 と同じ raw 実完備化のデータ。
R=A ⧸ W.ideal、fR=f.map (Ideal.Quotient.mk W.ideal)、
S=PowerRootEquationQuotient p hp fR、cS と rS はこの商の係数射・標準根列とする。
`existsUnique_powerRootPrismMonicCompletionHom_of_equation_input` の引数は
{B : Type u} [CommRing B]、Q : OrientedPrism p B、
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0、
k : OrientedPrism.Hom W Q、η : S →+* B ⧸ Q.ideal、hη : η.comp cS=k.quotientMap。
元の H の環構造 `pdCompletionCommRing L p (jL dP)` を let で導入した後の結論は

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f)=k.toRingHom ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n))))=η (rS n)
```

である。標準根列の互換性と fR の方程式を η で写し、係数射との可換性から
元の f の剰余方程式を得て、E1.69 の普遍射を使う。
試験 prism の完全性・p 正則性、生成元の厳密な保存、源の prism 商の p 正則性、
f のモニック性・正次数はこの普遍射には不要。

BS Rem 7.15（著者版 p.62）の完備入力環への接続を目的とする、原典とは異なる
具体的な通常の商・根列抽出による経路を docstring に明記した。
ここでの S は未完備の通常の商であり、原典の完備入力環との同一視をしていない。
完備化とモニック商の交換、原典の完備 S との同定、源 H 自体の prism 性、
raw と実完備化の正則性・完全忠実平坦性に残る hpR、原典の係数表記との最終照合は未完了。
絶対 prismatic envelope 全体の同定とはまだ数えない。
承認済み hdeg を持つ任意族存在定理の型は変更していない。

検証：新規 2 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4566 jobs）。新規 8 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 7056 宣言の推移的公理依存は標準 3 公理のみ。
新規 8 公開宣言の正確な型を `#check` で確認した（終了コード 0）。

## 並列分割の受渡し（2026-10-17）

本節は依頼に基づく A1-a からの一度限りの受渡し。参照時点は E1.70。
A1-a は源 H 自体の prism 性・完備入力環 S との接続・絶対 envelope 同定の合流を担当する。
A1-b は hpR 依存の解消、A1-c は原典の R/ϖ と実装の R/p の係数表記の最終照合を担当する。
A1-b・A1-c は Andre/ の既存ファイルを変更せず、新規ファイル・別名で公開する。
既存 hpR 付き定理の差替えは成果到着後に A1-a が行う。それまでは既存定理を変更しない。
以下は A1-a の受渡し情報であり、他担当の記録節ではない。

### (1) A1-b：hpR を持つ公開定理と使用箇所

以下の名前はすべて名前空間 `SerrePositivity.BhattScholze.Andre` 内。
ファイルはすべて `SerrePositivity/BhattScholze/Andre/` からの相対パスで示す。
8 本の共通の暗黙引数と、順序付き明示引数は次の通り。
最初の 5 本は W, hW, hpR, f, hf、後の 3 本はさらに hdeg を持つ。

```lean
{A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
(W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
(hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
(f : Polynomial A) (hf : f.Monic)
-- 6–8 のみ
(hdeg : 0 < f.natDegree)
```

結論の略記は既存コードそのままの次の定義を使う。これらを展開すれば正確な型となる。
`pdCompletionCommRing` は各結論の let で導入される構造を使う。

```lean
hp := Nat.Prime.pos (Fact.out : p.Prime)
P := PowerRootPolynomial A p hp
E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
dP := algebraMap A P W.generator
a := powerRootPrismMonicUnaryFamily (p := p) f
L := DeltaAdjoinDivision E dP a
Raw := L
jL := deltaAdjoinDivisionMap E dP a
dL := jL dP
H := PDCompletionH0 L p dL
uL := pdCompletionUnit L p dL
T := H ⧸ Ideal.span {uL dL}
R := A ⧸ W.ideal
```

1. `powerRootPrismMonicRaw_p_mul_injective` — `PowerRootPrismMonicRawRegular.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicRaw_p_mul_injective :
    Function.Injective (fun r : Raw => (p : Raw) * r)
```

hpR の使用：証明末尾の `deltaDivisionUnaryRaw_p_mul_injective` に `powerRootPrismGenerator_modPrime_regular p W hW hpR` を渡す。元の係数環で d mod p が正則という、有限段帰納の入力。

2. `powerRootPrismMonicRaw_mod_prime_generator_regular` — `PowerRootPrismMonicRawPairRegular.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicRaw_mod_prime_generator_regular :
    IsSMulRegular (Raw ⧸ Ideal.span {(p : Raw)})
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (deltaAdjoinDivisionMap E dP a dP))
```

hpR の使用：証明末尾の `deltaDivisionUnaryRaw_mod_prime_d_regular` に同じ `powerRootPrismGenerator_modPrime_regular p W hW hpR` を渡す。

3. `powerRootPrismMonicRaw_pdCompletion_generator_regular` — `PowerRootPrismMonicRawPairRegular.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular :
    let dL := deltaAdjoinDivisionMap E dP a dP
    letI := SerrePositivity.DerivedCompletion.pdCompletionCommRing Raw p dL
    IsSMulRegular (SerrePositivity.DerivedCompletion.PDCompletionH0 Raw p dL)
      (SerrePositivity.DerivedCompletion.pdCompletionUnit Raw p dL dL)
```

hpR の使用：`principalPair_pairCompletion_second_regular` の二つの入力に、上記 raw p 正則性と mod p 分母正則性（ともに hpR 付き）を使う。A1-a の H の prism 性に直接必要な正則性はこの結論。

4. `powerRootPrismMonic_pdCompletion_prime_regular` — `PowerRootPrismMonicCompletionRegular.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonic_pdCompletion_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular H (p : H)
```

hpR の使用：`principalPair_pairCompletion_first_regular` に同じ raw 正則対を渡す。

5. `powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular` — `PowerRootPrismMonicCompletionRegular.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular :
    let := pdCompletionCommRing Raw p dL
    IsSMulRegular (H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
      (p : H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL})
```

hpR の使用：`principalPair_pairCompletion_mod_second_first_regular` に同じ raw 正則対を渡す。これは H/d 自体の p 正則性という強い中間結論。

6. `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat` — `PowerRootPrismMonicHodgeTateCompletelyFaithfullyFlat.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T
```

hpR の使用：`powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat W hW hpR f hf hdeg` を経由。後者（`PowerRootPrismMonicHodgeTateCompletelyFlat.lean`）では hpR から基底の ϖ 正則性を得る `regular_of_span_power_eq` と、H/d の p 正則性から得る `powerRootPrismMonicHodgeTate_varpi_regular` の二箇所で使う。

7. `powerRootPrismMonicCompletion_pair_completelyFlat` — `PowerRootPrismMonicCompletionPairFlat.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicCompletion_pair_completelyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicCompletionAlgebra W hW f
    IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H
```

hpR の使用：`hreg` に 3 の H 上の d 正則性、`hred` に 6 の H/d の p 完全忠実平坦性を使い、`completelyFlat_pair_algebra_of_regular_reduction` に渡す。

8. `powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat` — `PowerRootPrismMonicCompletionPairFaithful.lean`。上記の明示引数を適用した結論：

```lean
theorem powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), W.generator})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))).obj
        (baseChangeScalarModule (powerRootPrismMonicCompletionBaseMap W hW f)))
```

hpR の使用：`hred` の証明に 6 の H/d の p 完全忠実平坦性を使い、`pairScalarExtension_faithfullyFlat_of_principal_reduction` に渡す。

8 の導来 H⁰ への移送先は同ファイルの
`powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat`。
H の prism 構造を現在与える `powerRootPrismMonicCompletionPrism`
（`PowerRootPrismMonicCompletionPrism.lean`）は、`OrientedPrism.ofDistinguished` へ
3 を渡す箇所だけで hpR を使う。δ 構造、distinguished 性、p と d の導来完備性、
標準係数射は hpR 不要。A1-a との最小の接続点は **元の H と元の dH=uL dL の正則性**。
同じ H のまま 3 と 6–8 に相当する追加 hpR 不要の成果を別名で公開すると合流しやすい。

注意：8 本すべてから文字通り hpR を削除することは目標ではない。
たとえば d=p の場合、2 の mod p の d は 0 となり、非零商で正則ではない。
5 の H/d の p 正則性も標数 p の非零 H/d に対して成り立たない。
これらは既存の hpR 付き経路での中間主張であり、一般の場合には別の正則性・
導来剰余の計算へ置き換える必要がある。候補を p ねじれ除去商へ取り替えたり、
元の R の p 正則性を存在定理へ追加したりせず、主張が正しい最終接続点を優先する。
現在の任意族存在定理の承認済み hdeg は維持する。

### (2) A1-c：R/ϖ 側と R/p 側の対応・未照合命題

ここでは d=W.generator、x=perfectPrismVarpiLift W hW=φ_A⁻¹(d)、
R=A/(d)、ϖ=perfectPrismVarpi W hW、Rv=R/(ϖ)、Rp=R/(p)、
bv:A→Rv と bp:A→Rp は標準二重商射、Nv=PowerRootPolynomial Rv p hp、
Np=PowerRootPolynomial Rp p hp とする。
`Mv := T ⧸ Ideal.map (powerRootPrismMonicHodgeTateBaseMap W hW f) (Ideal.span {ϖ})`
は自然な係数作用を持つ**実際の T/ϖ**。
fInv=perfectPrismInverseFrobeniusPolynomial W hW f は係数に φ_A⁻¹ を作用させた多項式。
`PD` は `PrincipalDPPresentation`、その正次数イデアル上の実分冪構造を指す。

| R/ϖ 側の既存結果・ファイル | R/p 側または接続先 |
|---|---|
| `perfectPrismVarpiLift`, `_frobenius`, `perfectPrismVarpi`, `_pow`, `_span_pow`, `perfectPrismVarpiLift_pair_span` — `PerfectPrismVarpi.lean` | (ϖ^p)=(p)、(p,x)=(d,x) の基底関係。`perfectPrismVarpiQuotientEquiv` も同ファイル。 |
| `perfectPrismVarpiRootInputEquiv`, `_coeff`, `_variable`, `_input` — `PerfectPrismVarpiRootInput.lean` | mod p の無限根環を x で割った表示を Nv へ同定。`perfectPrismVarpiRootInput_monic_regular` がモニック入力の正則性。 |
| `perfectPrismVarpiPDEnvelopeEquiv`, `_coeff`, `_generator`, `_input`, `_positiveIdeal` — `PerfectPrismVarpiPDComparison.lean` | `PowerRootCoefficientPDEnvelope` の x 還元を PD_Nv(f mod ϖ) に同定。 |
| `perfectPrismVarpiNativePDEnvelope_truncatedEquiv`, `_free_over_powerQuotient`, `_free`, `_faithfullyFlat`, `perfectPrismVarpiRootInput_free`, `perfectPrismVarpiRootPowerQuotient_free`, `_truncated_dpow` — `PerfectPrismVarpiNativePDFlat.lean` | Rem 7.15(1)(2) の切断多項式表示、Nv/(f^p) 上の自由性、Rv 上の自由性・忠実平坦性。f はこの表の行では元の f mod ϖ。 |
| `perfectPrismVarpiNativeDividedPowersOfMonic`, `_base_apply`, `existsUnique_perfectPrismVarpiNativePDMorphismOfMonic` — `MonicPerfectPrismPDEnvelope.lean` | `powerRootPrimeFrobeniusDividedPowersOfMonic`, `_base_apply`, `existsUnique_powerRootPrimeFrobeniusPDMorphismOfMonic` — 同ファイル。両側とも hpR 不要。比較に使う Rv 側の入力は **fInv mod ϖ**。 |
| `perfectPrismVarpiFrobeniusQuotientEquiv`, `_mk`, `_mk_pow`, `perfectPrismVarpiFrobenius_pairIdeal` — `PerfectPrismVarpiFrobeniusQuotient.lean` | e:Rv≃+*Rp、e(bv(a))=bp(φ_A(a))。単なる自然商射ではない。 |
| `powerRootPrismInverseVarpiPDEquiv`, `_coeff`, `_generator`, `powerRootPrismMonicVarpiCompletionPDEquiv`, `_coeff`, `_base_coeff` — `PowerRootPrismMonicVarpiPDComparison.lean` | 完備化の (d,x) 商を PD_Nv(fInv mod ϖ) へ同定。 |
| `powerRootPrismMonicVarpiResidueAlgEquiv`, `powerRootPrismMonicVarpiResidueAlgebra_base_coeff`, `_free`, `_faithfullyFlat` — `PowerRootPrismMonicVarpiFlat.lean` | 実 Mv と Rv 上の逆係数入力の PD 表示。自然な Rv 作用の比較。 |
| `powerRootVarpiPrimeFrobeniusEquiv`, `_coeff`, `_variable`, `_input`, `varpiPrimeFrobenius_inverse_coeff` — `PowerRootVarpiPrimeFrobeniusPD.lean` | e を係数ごとに延長し、fInv mod ϖ を f mod p へ送る。根変数の添字はこの係数比較そのものでは変わらない。 |
| `powerRootVarpiPrimeFrobeniusPDEquiv`, `_coeff`, `_generator` — `PowerRootVarpiPrimeFrobeniusPD.lean` | PD_Nv(fInv mod ϖ) ≃+* PD_Np(f mod p)。 |
| `powerRootPrismMonicVarpiFrobeniusResidueEquiv`, `_coeff`, `powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv`, `_tmul` — `PowerRootPrismMonicFrobeniusBaseChange.lean` | U:Mv≃+*Dp は e 半線形。Rp⊗[Rv,e]Mv≃ₐ[Rp]Dp。Dp=PD_Np(f mod p)。 |
| `powerRootPrismMonicVarpiFrobeniusResidueEquiv_variable`, `_variable_succ`, `powerRootPrismMonicVarpiFrobeniusBaseChangeAlgEquiv_variable` — `PowerRootPrismMonicFrobeniusRootAction.lean` | 実入力の Y_n を U で送ると (Y_n)^p、Y_(n+1) なら Y_n。係数だけの比較とは異なり根の段が一つずれる。 |
| `powerRootPrismMonicVarpiBaseMap`, `_coeff`, `powerRootPrismMonicVarpiFrobeniusResidueEquiv_base_coeff`, `powerRootPrismMonicFullFrobeniusPullbackAlgEquiv`, `_tmul`, `_variable` — `PowerRootPrismMonicFullFrobeniusPullback.lean` | A 全体の φ_A 引戻しを実装した型 At=TensorBaseCopy A⊗[A]Mv と Dp の左 A 線形同型。左 A 作用は φ_A、右は自然な qA:A→Mv。 |
| `powerRootPrismMonicFullFrobeniusDividedPowersOfMonic`, `powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphismOfMonic`, `powerRootPrismMonicFullFrobeniusDividedPowersOfMonic_input_apply`, `existsUnique_powerRootPrismMonicFullFrobeniusPDMorphismOfMonic` — `PowerRootPrismMonicFullFrobeniusPDOfMonic.lean` | 実 At 上の分冪構造と Np 上の pd 普遍性。hpR 不要。原典の係数表記の最終照合は未宣言。 |

照合すべき命題は次の通り。

1. 原典 Rem 7.15(1)（著者版 p.62）の φ_A^*(T/ϖ) の左 A 作用・右 A 作用・ϖ の選択を、実装の qA と φ_A に一つずつ対応させる。`TensorBaseCopy A` はスカラー作用の衝突を防ぐ型の写しにすぎない。
2. その引戻しにおいて係数イデアルが (d,x) から φ_A(d,x)=(p,d) に移る計算と、原典が R/ϖ と書く係数環との対応を正確に述べる。現在の full pullback の自然な左係数商は Rp。単に Rp を Rv に置換してはならない。
3. 元の f mod ϖ、逆係数の fInv mod ϖ、元の f mod p の三者を区別し、e を通した多項式の式を確定する。原典の f をどの係数作用で読むかが要点。
4. 元の入力 Y_n の自然像と、pd 包の Y_n の像を照合する。実 U では Y_n↦Y_n^p、Y_(n+1)↦Y_n という式を保持する。
5. 単なる環同型・係数環上の代数同型・入力無限根環 Np 上の pd 普遍性の三段階を区別し、原典と同じ入力環作用を持つ pd 包としての最終命題を新規ファイル・別名で公開する。既存の OfMonic 系の構造と普遍性を再利用できる。
6. 原典側の表記を調整する必要があると判断した場合は、原典の主張を無断で書き換えず、対応する正確な式と理由を記録し A1-a へ渡す。BS Cor 8.12 は前提・宣言・使用のいずれにも入れない。

A1-a での現在の接続点：E1.69 は任意の基底 prism 射 k と有界試験 prism Q に対する
剰余根列を保つ H→B の一意な δ 射、E1.70 は未完備の通常の入力環
(A/d)[Y^(1/p^∞)]/(f) から Q の商への射による同じ普遍性。
原典の完備入力環の同定と H 自体の prism 化を担当し、A1-b・A1-c の新規成果で合流する。

### E1.71／A1-a 方程式商の p 完備化からの入力射（2026-10-17）

本節は並列分割後の A1-a の追記。上記の一度限りの受渡し後、
通常の入力商の p 完備化と有界試験 prism への普遍性を接続した。
既存の hpR 付き定理と A1-b・A1-c のファイル・記録節は変更していない。

新規 `Andre/PrimeAdicCompletionUniversal.lean` の 2 公開定理の型は、
(R : Type u) [CommRing R] (p : ℕ)、{B : Type v} [CommRing B]、
[IsAdicComplete (Ideal.span {(p : B)}) B]、C=AdicCompletion (Ideal.span {(p : R)}) R
の下で以下。宇宙 u と v は独立。

```lean
-- existsUnique_primeAdicCompletionHom R p (k : R →+* B)
∃! F : C →+* B, F.comp (algebraMap R C) = k
-- primeAdicCompletion_ringHom_ext R p (F G : C →+* B)
--   (h : F.comp (algebraMap R C) = G.comp (algebraMap R C))
F = G
```

指定した環射の代数作用を使い、既存の `adicCompletion_existsUnique_algHom`
（`SerrePositivity/CommutativeAlgebra/AdicCompletionAlgebraUniversal.lean`）を再利用する。
イデアルの像は環射が自然数を保存することにより標的の (p) に一致する。
p の素数性、源や標的の p 正則性、Noether 性はいずれも不要。

新規 `Andre/PowerRootEquationCompletionUniversal.lean` の 1 公開定理
`existsUnique_powerRootEquationCompletionHom` は、
{R : Type u} [CommRing R]、p : ℕ、hp : 0 < p、f : Polynomial R、
{B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]、
k : R →+* B、ρ : ℕ → B、hρ : ∀ n, ρ (n+1)^p=ρ n、
hf : f.eval₂ k (ρ 0)=0 の下で、
S=PowerRootEquationQuotient p hp f、C=AdicCompletion (Ideal.span {(p : S)}) S、
j=algebraMap S C、c=powerRootEquationQuotientCoeff p hp f、
r=powerRootEquationQuotientRoot p hp f として、正確に

```lean
∃! F : C →+* B, (F.comp j).comp c = k ∧ ∀ n, F (j (r n)) = ρ n
```

を証明する。通常の方程式商からの一意な射を、新しい完備化の普遍性で延長する。
モニック性・正次数を仮定せず、係数射と全ての標準根の像を保つ。

新規 `Andre/PowerRootPrismMonicCompletedEquationInput.lean` の 1 公開定理
`existsUnique_powerRootPrismMonicCompletionHom_of_completed_equation_input` は、
完全な源 prism W : OrientedPrism p A、hW、f : Polynomial A、p の素数性の下で、
E1.70 と同じ P、E、dP、a、L、jL、H、uL、DH を使う。
R=A ⧸ W.ideal、fR=f.map (Ideal.Quotient.mk W.ideal)、
S=PowerRootEquationQuotient p hp fR、C=AdicCompletion (Ideal.span {(p : S)}) S、
jS=algebraMap S C、cS と rS は S の標準係数射・根列とする。
引数は {B : Type u} [CommRing B]、Q : OrientedPrism p B、
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0、
k : OrientedPrism.Hom W Q、η : C →+* B ⧸ Q.ideal、
hη : (η.comp jS).comp cS=k.quotientMap。
H の環構造 `pdCompletionCommRing L p (jL dP)` を let で導入した後の結論は

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (jS (rS n))
```

である。完備入力射を通常の商へ制限し、E1.70 の普遍性を使う。
hpR、モニック性・正次数、試験 prism の完全性・p 正則性を要求しない。

BS Rem 7.15（著者版 p.62）への接続として、通常の商を先に完備化する
原典とは異なる明示的な経路であることを docstring に記録した。
現在の C は (R[Y^(1/p^∞)]/(f)) の p 完備化であり、原典の
R⟨Y^(1/p^∞)⟩/(f) との同定をまだ主張しない。モニック性を使う完備化と商の交換、
元の H の prism 化、入力環作用を含む絶対 envelope の同定は A1-a の残り。
H の正則性の無条件の供給は A1-b、係数表記の最終照合は A1-c の成果と合流する。
この段階を A1-a 全体の完成とは数えない。

検証：新規 3 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4569 jobs）。新規 4 公開宣言の `assert_no_sorry` と専用監査は
終了コード 0。生成宣言を含む 7138 宣言の推移的公理依存は標準 3 公理のみ。
新規 4 公開宣言の正確な型と、受渡しの hpR 付き 8 定理の型を `#check` で確認した
（いずれも終了コード 0）。受渡し節は再作成・書換えしていない。

## A1-b：hpR の解消

2026-10-17。既存 Andre/ ファイルと他担当節は変更しない。
新規成果はすべて `Andre/Unconditional/` に置き、差替えは A1-a に委ねる。
元の H・分母商に関する A1-a の最小接続点は証明・監査済み。
raw 自身とその古典的 p 完備化の正則性も、末尾の無条件版で解消した。
以下の途中記録の残課題は履歴であり、完了時の分類は本節末尾を正本とする。
主定理・引用件数は変更しない。

### 原典の適用範囲と分類の基準

BS Rem 7.15、著者版 p.62
（https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=62）を確認した。
原典は ind-syntomic 性の計算を基底変更で p ねじれなしの場合へ帰着してから行う。
一般の perfectoid 環 R=A/(d) が p 正則、という意味ではない。
従って、(c) の正則性補題はこの帰着後なら hpR を定義どおりに供給できるが、
帰着前の R に自動的に供給したとは主張しない。

(a) は証明内で hpR が使われない場合、(b) は既存の弱い性質で代替した場合、
(c) は結論そのものが一般には成立しない場合とする。
現行証明で使っているというだけで (c) に分類しない。

### (b) 射影的正次数商で解消した 17 宣言

コミット `4c97d497` の方法を用いる。旧証明の hpR は
`perfectPrismVarpiLift_modPrime_regular` を経由して係数元の正則性を供給していた。
モニック入力の正次数商の自由性・射影性と商射の線形切断で代替し、
同じ実商環・分冪イデアル・入力環作用を保つ。新しい仮定はない。
Native、Prime、Full の既存 OfMonic 版も再利用した同じ証明経路である。
以下は旧名の末尾に `_of_unconditional` を付けて新規公開した名前の一覧。

- `perfectPrismVarpiPowerRootDividedPowers_of_unconditional`
- `perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional`
- `perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional`
- `perfectPrismVarpiNativeDividedPowers_of_unconditional`
- `perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional`
- `existsUnique_perfectPrismVarpiNativePDMorphism_of_unconditional`
- `powerRootPrimeFrobeniusDividedPowers_of_unconditional`
- `powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional`
- `existsUnique_powerRootPrimeFrobeniusPDMorphism_of_unconditional`
- `powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional`
- `powerRootPrismMonicFrobeniusTensorInputAlgEquiv_isDPMorphism_of_unconditional`
- `powerRootPrismMonicFrobeniusTensorDividedPowers_input_apply_of_unconditional`
- `existsUnique_powerRootPrismMonicFrobeniusTensorPDMorphism_of_unconditional`
- `powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional`
- `powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphism_of_unconditional`
- `powerRootPrismMonicFullFrobeniusDividedPowers_input_apply_of_unconditional`
- `existsUnique_powerRootPrismMonicFullFrobeniusPDMorphism_of_unconditional`

型は、元の完全 prism W、完全性 hW、f とモニック性 hf を保持する。
構造の結論は元の指定イデアル上の `DividedPowers`、値の公式は全 n、
分冪射性は元の比較射、普遍性は任意宇宙の分冪標的への `∃!` を保持する。
ファイルは `VarpiPDReduction`、`MonicPDEnvelope`、`FrobeniusTensorPD`、`FullFrobeniusPD`。

### PowerRootMonicPDFlat の同名引数は別条件

同ファイルの二つの hpR は `IsSMulRegular R p` ではなく `(p : R)=0` である。
この標数条件自体を一般の係数環から除去したとは主張しない。
原典の実係数環 Rv=(A/W.ideal)/(ϖ) では `(ϖ^p)=(p)` から p=0 を内部供給した。
`Unconditional/MonicPDFlat.lean` の
`powerRootMonicDPPresentation_free_of_unconditional` と
`powerRootMonicDPPresentation_faithfullyFlat_of_unconditional` はこの Rv に対する版。
後者は元の正次数 hdeg を保持し、R の p 正則性は仮定しない。
`perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional` が自動供給の証明である。

### (c) 結論が一般には成立しない正則性補題

`Unconditional/RegularityBoundary.lean` で次の同値を証明した。

- `perfectPrism_generator_modPrime_regular_iff`：d mod p の正則性 ↔ hpR。
- `perfectPrismVarpiLift_modPrime_regular_iff`：φ⁻¹(d) mod p の正則性 ↔ hpR。

逆向きは完全 δ 環の p 正則性と正則対の順序交換を使う。
従って次の旧名を単に無条件化することはしない。

- `perfectPrism_generator_modPrime_regular`
- `perfectPrismVarpiLift_modPrime_regular`
- `powerRootPrismGenerator_modPrime_regular`
- `powerRootPrismFirstModPrimeRelation_regular`
- `powerRootPrismMonicFirstModPrime_generator_regular`
- `powerRootPrismMonicFinite_all_regular`

後二つは mod p の d 正則性を結論に含む。d=p、f=Y の crystalline な場合には、
非零な対応商でその元は零となる。任意 f の最初の線形関係の正則性も、
d=p、f=0 では mod p で零となり一般には成立しない。
`not_prime_regular_of_charP` は非零な標数 p 環では p が正則でないことを形式的に確認する。

受渡しの `powerRootPrismMonicRaw_mod_prime_generator_regular` と
`powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular` も同じ強い中間主張である。
原典の p ねじれなしへの帰着後の使用と、帰着前に必要な弱い入力の供給を区別する。

### 無条件の弱い入力と残る接続

`perfectPrism_generator_power_bounded_torsion_of_unconditional` は
任意 n,N と x∈A/(d^n) について p^N x=0 なら p^n x=0 を供給する。
完全性、p 進分離性、distinguished 元の既存定理を使い、hpR は不要。
これを p 正則性へ強めたとは扱わない。

`Unconditional/PowerRootResidueKoszul.lean` は元の P、δ 構造 E、dP、
分子 a=f(Y₀) と同じ一元自由 δ 環 L₀ を保持する。
初期の mod(p,d) 関係は負のモニック入力なので hpR なしに正則。
その後の全有限 δ 関係列は既存の Witt 計算により弱正則で、Koszul 分解を与える。
実評価列との三角比較と G7 の Tor の逐次余極限保存により、
`powerRootPrismMonicResidueSource_tor_subsingleton_of_unconditional` は
実射 ψ=(L₀→L₀/(p,dP))∘deltaDivisionSourceMap E dP に沿う全評価環 P の
全正次数 `TorAlg ψ (i+1) P` が Subsingleton であることを供給する。
G7 の交換条件は内部で証明済みの API から供給し、仮定に残さない。

`Unconditional/PowerRootResidueSource.lean` は Tor 対称性と標準 augmentation により、
同じ実残余源の β に沿う導来評価を元の raw (p,d) 剰余の single に同定する。
これは P 上の比較であり、まだ元の A 上の実逐次完備化との同定ではない。

次の旧名は完成した (b) とも本質的な (c) とも断定せず、引き続き解消対象とする。

- `powerRootPrismMonicRaw_p_mul_injective`：現行証明は d mod p 正則性を有限段帰納へ渡す。
  上の残余 Koszul 計算だけで raw の p 正則性が従うとは主張しない。
- `powerRootPrismMonicRaw_pAdic_regular_pair`：古典的 p 完備化での p と d の個別正則性。
  mod p の d 正則性を結論する定理ではないので、(c) へ混同しない。
- `powerRootPrismMonicRaw_pdCompletion_generator_regular`：現行証明は raw の正則対を使う。
- `powerRootPrismMonic_pdCompletion_prime_regular`：同じ raw 正則対を使う。
- `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat`：現行証明は基底と T の ϖ 正則性を使う。
- `powerRootPrismMonicCompletion_pair_completelyFlat`：上の分母正則性と T の完全平坦性を使う。
- `powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat`：T の完全忠実平坦性を使う。

次の具体的作業は、実残余源の比較を元の A 係数作用へ制限し、
p,d の逐次完備化単位の比較へ接続すること。その後、生成元冪商の有界 p ねじれと
導来完備性による純性・正則性を使い、同じ H と同じ dH のまま A1-a の最小接続点を供給する。
特に H の分母正則性と完全忠実平坦性の無条件版は、この時点では未完了である。

### 最初の検証区切り

上記 8 新規ファイルの 32 公開宣言について
`scripts/audit_andre_unconditional.lean` の全件 `assert_no_sorry` と
値・型の推移的公理依存走査が終了コード0で成功した。
44,835 宣言を走査し、許可公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`lake build SerrePositivity.BhattScholze.Andre.MonicRootedExtension` を含む
全新規対象のビルドも4577ジョブで成功した。
ここで保存するのは検証済みの途中成果であり、上記の未解消接続を完了したとはしない。



### A1-d 受領後の実逐次完備化の純性（2026-10-17）

A1-d の `InitialCoefficient.rawResidue_faithfullyFlat` と
`InitialCoefficient.sourceResidueH0_faithfullyFlat` を受領した。
証明本体は `8e0a2a6a`・`18de67e0`、独立監査は `5c623cf9`。
`Unconditional/InitialCoefficient/` のファイルは本系列では編集していない。

新規 `Unconditional/PowerRootSourceComplete.lean` と
`Unconditional/PowerRootSourcePurity.lean` に 17 公開宣言を追加した。
`X := PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f`
は元の A 上の二因子源を p,d の順に実導来完備化した対象そのもの。

- `powerRootPrismMonicSourceIteratedPDCompletion_isComplete_p_of_unconditional` と
  `powerRootPrismMonicSourceIteratedPDCompletion_isComplete_d_of_unconditional`：X の両方向の導来完備性。
- `powerRootPrismMonicSourceIteratedPDReductionIso_of_unconditional`：X の実 (p,d) 還元と元の源の還元との同型。
- `powerRootPrismMonicSourceCanonicalPowerResidueH0_faithfullyFlat_of_unconditional`：
  A1-d の H⁰ 忠実平坦性を実完備化後・標準冪零剰余へ移す。入力仮定は解消済み。
- `powerRootPrismMonicSourcePowerResidue_pure_flat_of_unconditional`：
  任意 n>0 で実 A/(p,dⁿ) 還元の純性と H⁰ の平坦性。
- `powerRootPrismMonicSourceGeneratorPowerReduction_pure_bounded_of_unconditional`：
  任意 n>0 で実 A/(dⁿ) 還元の純性と H⁰ の有界 p ねじれ。
- `powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional`：
  f.Monic と 0<f.natDegree の下で、正確に
  `X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective (fun x :
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj => W.generator • x)`。
- `powerRootPrismMonicSourceSingleIso_of_unconditional`：X と同じ H⁰ の single の正規化同型。

hpR・raw p 正則性・新引用は使わない。元の H の分母正則性への移送と
H/dH の p 完全忠実平坦性、H の (p,d) 完全平坦性は次の接続に残す。

検証：`MonicRootedExtension` を含む対象ビルドは終了コード 0（4594 jobs）。
専用監査は既存分と合わせた 82 公開宣言の `assert_no_sorry` と型・値の推移的依存検査に成功。
47,737 宣言を走査し、公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。



### 元の H・分母商への移送と標準二元剰余（2026-10-17）

純性の保存コミット `a9f224bd` に続き、新規 9 ファイルの 56 公開宣言を追加した。
置き場所はすべて `Andre/Unconditional/`。既存 André ファイルと A1-d のファイルは変更していない。
標準テンソル augmentation の抽象補助定理を使い、元の源の H⁰ と raw PD 環を
元の A 線形作用のまま比較した。具体的な完備化単位の比較も保存している。

正確な共通設定は、完全 prism W、`hW : W.deltaStructure.IsPerfect`、
`f : Polynomial A`、`hf : f.Monic`、`hdeg : 0 < f.natDegree`。
`P := PowerRootPolynomial A p hp`、`E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure`、
`dP := algebraMap A P W.generator`、`a := powerRootPrismMonicUnaryFamily (p := p) f`、
`L := DeltaAdjoinDivision E dP a`、`jL := deltaAdjoinDivisionMap E dP a`、
`H := PDCompletionH0 L p (jL dP)`、`dH := pdCompletionUnit L p (jL dP) (jL dP)`、
`T := H ⧸ Ideal.span {dH}`、`R := A ⧸ W.ideal` とする。
H の環構造は元の `pdCompletionCommRing L p (jL dP)` であり、対象を変更していない。

主要な公開名・型は次のとおり（共通名前空間 `SerrePositivity.BhattScholze.Andre`）。

- `powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f`：
  実逐次完備化の H⁰ と、元の L 加群 H を A へ係数制限した加群との A 線形同型。
  この比較自体には hf・hdeg は不要。
- `powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional W hW f hf hdeg`：
  上記環構造の下で `IsSMulRegular H dH`。
- `powerRootPrismMonicHodgeTateDerivedReductionIso_of_unconditional W hW f hf hdeg`：
  実逐次完備化の A→R に沿う実導来還元と、自然な R 作用を持つ T の single の同型。
- `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional W hW f hf hdeg`：
  既存の `powerRootPrismMonicHodgeTateAlgebra W hW f` の下で、
  正確に `IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T`。
- `powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional W hW f hf hdeg`：
  `∃ N : ℕ, ∀ k : ℕ, ∀ x : T, (p : T)^k*x=0 → (p : T)^N*x=0`。
- `powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete_of_unconditional W hW f hf hdeg`：
  `IsAdicComplete (Ideal.span {(p : T)}) T`。
- `powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional W hW f hf hdeg`：
  既存の `powerRootPrismMonicCompletionAlgebra W hW f` の下で、
  `IsCompletelyFlat (Ideal.span {(p : A), W.generator}) H`。

標準係数射 `baseH := powerRootPrismMonicCompletionBaseMap W hW f` と
`q := Ideal.Quotient.mk (Ideal.span {(p : A), W.generator})` に対しても、
`powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing_of_unconditional`、
`powerRootPrismMonicCompletion_pair_reduction_homology_isZero_of_unconditional`、
`powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional`、
`powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat_of_unconditional` を公開した。
元の `baseChangeScalarModule baseH` の標準 q 係数拡大の Tor 消滅・忠実平坦性と、
その実導来還元の全非零次数消滅・H⁰ 忠実平坦性であり、A1-c の係数照合へそのまま渡せる。

全結果に hpR・追加の平坦性・新引用はない。正次数は初期係数の忠実平坦性に使い、
原典 Rem 7.15（著者版 p.62）の正次数モニック入力に対する成果として述べる。
次数零までの生成元正則性の拡張は、この証明からは主張しない。
既存名の差し替えは A1-a に委ねる。

検証：`MonicRootedExtension` を含む対象ビルドは終了コード 0（4607 jobs）。
`scripts/audit_andre_unconditional.lean` は 138 公開宣言の `assert_no_sorry`、
`#print axioms`、追加 56 宣言の `#check`、型・値の推移的公理走査に成功した。
48,340 依存宣言を走査し、標準三公理 `propext`、`Classical.choice`、`Quot.sound` のみ。

残る分類・証明課題は raw の `powerRootPrismMonicRaw_p_mul_injective`、
`powerRootPrismMonicRaw_pAdic_regular_pair`、
`powerRootPrismMonic_pdCompletion_prime_regular` 等の p 正則性系列である。
今回の分母正則性・完全平坦性の完成を raw p 正則性の証明と混同しない。
また mod p の d 正則性や H/dH の p 正則性は既述の通り一般には成り立たず、
原典の p ねじれなしへの帰着後の強い主張として区別する。



### 先行 p 還元の純性と、正次数を追加しない H の正則性（2026-10-17）

新規 `Unconditional/PrimeReductionPurity.lean` の 12 公開宣言を追加した。
旧 `powerRootPrismMonic_pdCompletion_prime_regular` は hpR から raw の正則対を作り、
第一元正則性の反復完備化保存へ渡していた。この経路を使わず、(b) として解消した。

元の実逐次完備化を X、`Y := A/(p) ⊗ᴸ_A X` とする。
A/(p) は完全 δ 構造から被約であり、任意 n,x について dⁿx=0 なら dx=0。
従って Y の d 還元の純性・H⁰ 平坦性、Y の商環上の d 導来完備性を
既存の有界ねじれ純性判定へ渡せる。
`powerRootPrismMonicSourcePrimeReduction_pure_of_unconditional` がその純性を供給し、
`powerRootPrismMonicSourceIteratedPDCompletion_prime_injective_of_unconditional` が
元の X の H⁰ 上で p が単射に作用することを供給する。
A→A/(p)→(A/(p))/(d) の標準主商比較は全係数を保持し、d mod p 正則性を仮定しない。

正次数のモニック入力について、元の A 線形 H⁰ 比較により
`powerRootPrismMonic_pdCompletion_prime_regular_of_positive_unconditional W hW f hf hdeg`
を得た。これは raw の p 正則性を仮定していない。

さらに、次数零モニック入力 f=1 の場合は、raw の除算関係が分母の乗法逆元を与える。
標準完備化射の像でもその逆元公式を保ち、H 自身の分母に関する導来完備性から H=0 を得る。
`powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero` がこの結果である。
これにより以下の二定理は、旧定理から hpR だけを除いた仮定で公開できた。
共通名前空間は `SerrePositivity.BhattScholze.Andre`。

- `powerRootPrismMonic_pdCompletion_prime_regular_of_unconditional W hW f hf`：
  元の `pdCompletionCommRing` の下で `IsSMulRegular H (p : H)`。
- `powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional W hW f hf`：
  同じ元の H の標準分母像 dH に対する `IsSMulRegular H dH`。

両者とも hdeg・hpR・raw p 正則性・追加の平坦性仮定は不要。
H/dH の p 完全忠実平坦性は従来どおり正次数の場合に述べる。
H の p 正則性から H/dH の p 正則性を結論したとはせず、その旧強条件は既述の (c) に残す。
原典 Rem 7.15（著者版 p.62）を補う、元の実対象の二方向の導来還元による経路である。

検証：`MonicRootedExtension` を含む対象ビルドは終了コード 0（4611 jobs）。
専用監査は合計 150 公開宣言の `assert_no_sorry`・`#print axioms` と追加宣言の `#check`、
48,382 依存宣言の型・値の推移的公理走査に成功した。
許可公理は `propext`、`Classical.choice`、`Quot.sound` の三つのみで、sorryAx はない。

この時点の未解消候補は `powerRootPrismMonicRaw_p_mul_injective` と
`powerRootPrismMonicRaw_pAdic_regular_pair`。
それらを本質的な (c) と断定せず、raw の有限段・局所化・完備化の証明調査を続ける。



### raw の深さ零の p 正則性とモニック初期線形関係（2026-10-17）

新規 `Unconditional/RawInitialRegular.lean` に 6 公開宣言を追加した。
旧有限段帰納法は、初期関係 dX-a の一次係数 d の mod p 正則性を hpR から得ていた。
この最初の非零因子判定には、定数係数 -a の正則性を使う別経路がある。
モニック入力 a=f(Y₀) は既存定理で mod p において正則なので、hpR は不要となる。

共通名前空間 `SerrePositivity.BhattScholze.Andre` の公開名は次のとおり。

- `unconditionalLinearPolynomial_regular_of_constant`：正則な定数係数を持つ一次多項式の正則性。
- `unconditionalLinearMvPolynomial_regular_of_constant`：任意の変数族に対する同じ判定。
- `unconditionalDeltaDivisionUnaryFirst_mod_prime_regular`：
  任意の一元 δ 除算源の初期関係は、分子の mod p 正則性だけで mod p 正則。
- `unconditionalDeltaDivisionUnaryFirst_prime_regular`：
  係数環の p 正則性と分子の mod p 正則性から、元の最初の関係商の p 正則性。
- `powerRootPrismMonicFinite_prime_regular_zero_of_unconditional W hW f hf`：
  正確に、`L₀ := PowerRootUnaryFreeDeltaRing A p hp`、
  `I := deltaDivisionFiniteRelationIdeal E dP a` として
  `IsSMulRegular (L₀ ⧸ I 0) (p : L₀ ⧸ I 0)`。
- `powerRootPrismFirstModPrimeRelation_regular_of_monic_unconditional W f hf s`：
  任意の変数族 τ と s:τ について、元の
  `C(dP mod p) * X s - C(powerRootMonicPDInput p f mod p)` の正則性。
  この定理には hW も hpR も不要。

いずれも正次数を仮定しない。多項式の非零因子判定は Mathlib の証明済みの係数判定による。
原典 Rem 7.15（著者版 p.62）のモニック入力に対する補足であり、新引用はない。
元の `powerRootPrismFirstModPrimeRelation_regular` は任意の非モニック f まで量化するため、
その署名から hpR を単純に外した定理と混同しない。hf は原典の入力で既に満たされる。
また、`powerRootPrismMonicFinite_all_regular` の mod p の d 正則性という第二成分を
無条件化したとはしない。今回証明したのは深さ零の p 正則性という第一成分である。

検証：監査が読む全担当モジュールと `MonicRootedExtension` の対象ビルドは
終了コード 0（4620 jobs）。専用監査は 156 公開宣言の `assert_no_sorry`・`#print axioms`、
追加宣言の `#check` と 48,403 依存宣言の型・値の推移的公理走査に成功した。
公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。

後続有限段の旧保存補題は mod p の d 正則性を明示入力にするため、初期値だけで
`powerRootPrismMonicRaw_p_mul_injective` を証明済みとはしない。
深さ 1 以降の関係の p 飽和性、および元の mod p 導来源の局所化・完備化による
純性検出を引き続き調べる。raw の二つの未解消候補の分類は変更しない。



### raw 源の局所化と完備化による負次数検出（2026-10-17）

新規 `Unconditional/SourceUnitDenominator.lean` の 9 公開宣言と
`Unconditional/CompletionTorsionDetection.lean` の 6 公開宣言を追加した。
いずれも BS Rem 7.15（著者版 p.62）の元の raw 源の比較のための補助結果。
既存 André ファイル・A1-d のファイル・他担当節は変更していない。

共通名前空間は `SerrePositivity.BhattScholze.Andre`。
前半では任意の δ 環 `D : DeltaStructure p A` と添字型 σ について、
元の `deltaDivisionSourceMap (σ := σ) D d` を用いる。
係数と初期変数上の計算および自由 δ 射の一意性から、以下を証明した。

- `unconditionalDeltaDivisionSourceMap_comp D d e`：
  `scale_d.comp scale_e = scale_(e*d)`。
- `unconditionalDeltaDivisionSourceUnitEquiv D u`（u:Aˣ）：
  `RelativeFreeDeltaRing (R := A) σ ≃+* RelativeFreeDeltaRing (R := A) σ`。
  順射は元の scale_u、逆射は scale_(u⁻¹)。
- `unconditionalDeltaDivisionSourceMap_bijective_of_isUnit D d hd`：
  `Function.Bijective (deltaDivisionSourceMap D d)`。
- `unconditionalRelativeFreeMap_isDeltaHom D E q hq` と
  `unconditionalDeltaDivisionSourceMap_natural D E q hq d`：
  元の多項式係数射が δ 構造を保ち、元の scale 射と可換。
- `unconditionalDeltaDivisionSourceMap_bijective_localization D d B`：
  `S := D.frobeniusDenominators (Submonoid.powers d)` に関する実局所化 B と
  既存の `D.localization S B ...` 上の scale_(algebraMap A B d) の全単射性。
- `unconditionalFrobeniusDenominators_isUnit_mod_prime D d q hp hd`：
  q(p)=0、q(d) が単元なら、S の全元も q で単元へ移る。
  終域の δ 構造は不要。
- `unconditionalFrobeniusDenominators_map_mod_prime D d q hp`：
  `S.map q.toMonoidHom = Submonoid.powers (q d)`。
- `unconditionalSaturatedLocalization_mod_prime_isLocalizationAway D d B`：
  `IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {(p:A)}) d)
    (B ⧸ (Ideal.span {(p:A)}).map (algebraMap A B))`。
  対象は実局所化 B の実商であり、別のねじれ除去商は使わない。

後半では任意の可換環 R、a:R、実対象 `X : ConcreteDerivedCategory R` を扱う。
`unconditionalScalarCone_homology_isZero` が隣接二次数の消滅を実スカラー錐へ移す。
完備化単位の Koszul 同値性から
`unconditionalNegativeHomology_smul_injective_of_completion_isGE` は
`(C_a X).IsGE 0 → i<0 → Function.Injective (fun x : H^i(X) => a • x)` を与える。
これを反復する
`unconditional_isGE_of_completion_isGE_of_negative_power_torsion` は、
`∀ i<0, ∀x:H^i(X), ∃n, a^n • x=0` から `X.IsGE 0` を得る。
対象自体の完備性・環の a 正則性・有界ねじれは不要であり、指数は各元で異なってよい。

通常局所化の核判定を使う
`unconditionalModule_power_torsion_of_localization_isZero` と、
実平坦導来係数拡大のホモロジー比較を使う
`unconditionalNegativeHomology_power_torsion_of_localization_isGE` を合成し、
最終的に `unconditional_isGE_of_completion_isGE_of_localization_isGE` を公開した。
正確な結論は、任意の `[IsLocalization.Away a B]` に対して
`(C_a X).IsGE 0 → (flatDerivedBaseChange (algebraMap R B) hflat |>.obj X).IsGE 0 → X.IsGE 0`。
hflat は局所化の平坦性から内部で供給する。新引用・sorry・axiom はない。

検証：監査が読む全担当モジュールと `MonicRootedExtension` の対象ビルドは
終了コード 0（4624 jobs）。専用監査は合計 171 公開宣言の `assert_no_sorry`、
`#print axioms`、追加 15 宣言の `#check`、48,763 依存宣言の型・値の推移的公理走査に成功。
公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。

未接続なのは、元の二因子導来源を上記の係数局所化上の二因子源へ運ぶ比較と、
同じ源の先行 p 還元の d 完備化を既証明の純粋な逐次完備化の p 還元へ比較する部分。
これらはまだ raw 全体の p 正則性の証明ではない。
`powerRootPrismMonicRaw_p_mul_injective` と `powerRootPrismMonicRaw_pAdic_regular_pair` の
無条件版を証明済みとも、本質的な (c) とも分類しない。担当 goal は継続中。



### 局所化先の純性と、元の右因子の標準係数拡大（2026-10-17）

`SourceUnitPurity.lean` の 5 公開宣言と `LocalizedScalarModule.lean` の 3 公開宣言、
`LocalizedDeltaSourceTarget.lean` の 1 公開宣言を追加した。
前節の 15 宣言は `6ea14f94` に保存済み。本単位も既存 André ファイルを変更しない。

`unconditionalSourceUnit_scalarModule_flat D d hd` は
`Module.Flat L (baseChangeScalarModule (deltaDivisionSourceMap D d))` を与える。
右因子の元の自己射作用は、逆環射を使う線形同型で通常の自由一階加群に移る。
`unconditionalSourceUnit_tor_isZero` はこの平坦性を Tor の対称性へ渡し、
任意の分子 a について元の β,α の二因子の全正次数 Tor を消す。
`unconditionalSourceUnit_augmentation_isIso` は元の標準 augmentation の同型性、
`unconditionalSourceUnit_homology_isZero` は同じ実二因子導来テンソルの全非零次数消滅。
`unconditionalSourceSaturatedLocalization_homology_isZero D d a B i hi` は、
係数・分母・分子をすべて標準局所化射の像として指定した実二因子源に適用する。
モニック性・完備性・p 正則性はこの局所化先の結果には不要。

`unconditionalScalarModuleCoefficientMap α β hcomm` の台写像は元の係数射。
分母集合 M を α が固定する場合、その射の `IsLocalizedModule M` を
`unconditionalScalarModuleCoefficientMap_isLocalizedModule` で証明した。
単元性・分数表示・核判定を元の作用へ移している。
その通常テンソル普遍性を使う `unconditionalScalarModuleLocalizationEquiv` の型は、
`[IsLocalization M S]`、α:R→+*R、β:S→+*S、
`hcomm : β.comp (algebraMap R S) = (algebraMap R S).comp α`、
`hfix : ∀s:M, α s=s` に対して
`(ModuleCat.extendScalars (algebraMap R S)).obj (baseChangeScalarModule α)
  ≃ₗ[S] baseChangeScalarModule β`。
自己射の平坦性や可逆性は仮定しない。

実 δ 源への適用 `unconditionalDeltaSourceTargetLocalizationEquiv D d B` は、
`T := D.frobeniusDenominators (Submonoid.powers d)`、
`E := D.localization T B ...`、`LA := RelativeFreeDeltaRing (R := A) σ`、
`LB := RelativeFreeDeltaRing (R := B) σ` として、正確に

```lean
(ModuleCat.extendScalars (MvPolynomial.map (algebraMap A B))).obj
    (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) ≃ₗ[LB]
  baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) E (algebraMap A B d))
```

を与える。源射は係数 C(T) を固定するので一般比較の仮定を内部で供給できる。
元の右因子を局所化先へ運ぶ部分はここで接続済み。
残るのは左の評価因子の同様の比較と、二因子導来テンソルへの合成、
先行 p 還元の d 完備化と既証明の逐次完備化の p 還元の比較である。
raw 全体と通常 p 完備化の正則性はまだ未証明であり、担当 goal は継続中。

検証：監査が読む全担当モジュールと `MonicRootedExtension` の対象ビルドは
終了コード 0（4630 jobs）。専用監査は 180 公開宣言の `assert_no_sorry`・
`#print axioms`、追加 9 宣言の `#check`、48,895 依存宣言の型・値の推移的公理走査に成功。
公理依存は標準三公理 `propext`、`Classical.choice`、`Quot.sound` のみ。



### 元の raw 全体の p 正則性：正次数モニック入力（2026-10-17）

新規 10 ファイルの 26 公開宣言を追加した。
`LocalizedEvaluationModule`、`LocalizedDeltaSourceEvaluation`、`LocalizedDeltaSourceTensor`、
`SourceUnitSingle`、`LocalizedDeltaSourcePrimeCone`、`SaturatedLocalizationTorsion`、
`SourcePrimeConeTorsion`、`ScalarConeRestriction`、`PowerRootRawPrimeConeCompletion`、
`PowerRootRawPrimeRegular`（すべて `Andre/Unconditional/`）が今回の成果である。
既存 André ファイルと A1-d のファイルは変更していない。

共通名前空間 `SerrePositivity.BhattScholze.Andre` の主要な公開名・型を記す。
完全 prism W、hW、f から作る元の対象を
`P := PowerRootPolynomial A p hp`、`E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure`、
`dP := algebraMap A P W.generator`、`a := powerRootPrismMonicUnaryFamily (p := p) f`、
`L := PowerRootUnaryFreeDeltaRing A p hp`、`Raw := DeltaAdjoinDivision E dP a`、
`X := PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f` とする。
X は元の二因子導来テンソルを元の標準 A 作用へ係数制限した対象であり、
Raw は元の δ 閉包による実商そのものである。

```lean
powerRootPrismMonicSourcePrimeCone_power_torsion_of_unconditional W hW f
    (i : ℤ) (hi : i ≠ 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedScalarConeFunctor A (p : A)).obj X.obj)) :
  ∃ n : ℕ, W.generator ^ n • x = 0

powerRootPrismMonicSourcePrimeConeCompletion_isGE_of_unconditional W hW f
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  ((derivedComplexCompletionFunctor A W.generator).obj
    ((derivedScalarConeFunctor A (p : A)).obj X.obj)).IsGE 0

powerRootPrismMonicSourcePrimeCone_isGE_of_unconditional W hW f
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  ((derivedScalarConeFunctor A (p : A)).obj X.obj).IsGE 0

powerRootPrismMonicRaw_p_mul_injective_of_positive_unconditional W hW f
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  Function.Injective (fun r : Raw => (p : Raw) * r)
```

最初の冪ねじれ性にはモニック性・正次数は不要。
局所化側では `unconditionalEvaluationLocalizationEquiv` が一般の評価射の実係数拡大を比較し、
`unconditionalDeltaSourceEvaluationLocalizationEquiv` が元の左評価因子へ適用する。
既存の右因子比較と平坦導来テンソルの係数拡大比較を合成した
`unconditionalDeltaSourceTensorLocalizationIso` により、元の実導来局所化と実二因子源が一致する。
単元分母の源は `unconditionalSourceUnitSingleIso` で元の評価加群の single と同型。
局所化した係数環の p 正則性を使う
`unconditionalDeltaSourcePrimeCone_localization_homology_isZero` が、元の p 錐の局所化後の消滅を与える。

`unconditionalSaturatedScalarCone_homology_power_torsion` は、元の実局所化の核判定と
実 p 錐のホモロジー上で p が零になることを合成する。
Frobenius 安定分母の mod p 像が元の分母の冪集合に等しいので、
一つの安定分母による零化を元の分母のある冪による零化へ戻せる。
これを実源へ適用した `unconditionalSourcePrimeCone_homology_power_torsion` と
`unconditionalBoundedRestrictionScalarCone_homology_power_torsion` で、元の標準 A 作用を保つ。
ねじれ指数の一様な上界・有限生成性・d mod p 正則性は仮定していない。

完備化側では `unconditionalIteratedCompletion_scalarConeIso` が、任意の a,b について
`C_a(Cone_b X) ≅ Cone_b(C_a(C_b X))` を元の完備化単位から構成する。
既証明の逐次完備化の先行 p 還元の純性を、この同型と実正則商 Koszul 比較で移す。
従って元の p 錐の d 完備化には負次数がない。
完備化単位の Koszul 同値性が負次数ホモロジー上の d 単射性を与えるので、
局所化側の d 冪ねじれと合流して元の p 錐の負次数が消える。
その H⁰ 上の p 単射性を `powerRootPrismMonicSourceRawStandardH0Iso_of_unconditional` で
元の標準 A 作用付き Raw へ移す。原典 BS Rem 7.15（著者版 p.62）を補う別経路であり、新引用はない。

今回の結論は正次数モニック入力に限る。元の旧定理は f=1 も含むため、
`powerRootPrismMonicRaw_p_mul_injective` の hpR を完全に解消したとはまだ数えない。
次数零入力の処理と `powerRootPrismMonicRaw_pAdic_regular_pair` の通常 p 完備化の正則対は残る。
どちらも本質的な (c) と断定せず、担当 goal は継続中。

検証：監査が読む全担当モジュールと `MonicRootedExtension` の対象ビルドは
終了コード 0（4654 jobs）。専用監査は 206 公開宣言の `assert_no_sorry`・
`#print axioms`、今回追加 26 宣言の `#check`、49,228 依存宣言の型・値の推移的公理走査に成功。
公理依存は標準三公理 `propext`、`Classical.choice`、`Quot.sound` のみで、sorryAx はない。



### 全モニック入力の raw p 正則性と通常 p 完備化の正則対（2026-10-17）

新規 `UnitNumeratorRawRegular.lean`、`RawPrimeRegularAllMonic.lean`、
`PrincipalSourceRegularity.lean`、`RawPrincipalH0Comparison.lean`、`RawPAdicPairRegular.lean` の
12 公開宣言を追加した。置き場所はすべて `Andre/Unconditional/`。
既存 André ファイルと A1-d のファイルは変更していない。

前節と同じ P,E,dP,a,Raw を用い、`j := deltaAdjoinDivisionMap E dP a`、
`CP := AdicCompletion (Ideal.span {(p : Raw)}) Raw` とする。
名前空間は `SerrePositivity.BhattScholze.Andre`。
新しい二つの置換先は、旧型から hpR だけを除いた次の型である。

```lean
powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f (hf : f.Monic) :
  Function.Injective (fun r : Raw => (p : Raw) * r)

powerRootPrismMonicRaw_pAdic_regular_pair_of_unconditional W hW f (hf : f.Monic) :
  let CP := AdicCompletion (Ideal.span {(p : Raw)}) Raw
  IsSMulRegular CP (p : CP) ∧
    IsSMulRegular CP (algebraMap Raw CP (j dP))
```

正次数仮定は不要。次数零モニック入力は f=1 なので、元の除算関係が j(dP) の逆元を与える。
`unconditionalRaw_prime_regular_of_unit_numerator` は、元の raw 包から
Frobenius 安定係数局所化への実 δ 射に左逆を作る。
係数環の p 正則性は平坦な局所化へ移り、その単射性によって元の raw 包へ戻る。
一般の単元分母包に置き換えず、元の δ 閉包商のままで証明している。

通常 p 完備化での p 正則性は raw p 正則性の主完備化保存から従う。
分母の正則性には、一般には偽の raw mod p 分母正則性を使わない。
`unconditionalHomology_regular_of_completionSingleIso` は、a 完備化が a 正則な single なら、
元の H⁰ でも a が単射になることを、元の完備化単位の a 錐同値性から証明する。
これを元の実 p 完備化源へ適用し、既証明の逐次完備化の純性・分母正則性を戻す。
`powerRootPrismMonicSourcePrincipalH0Iso_of_unconditional` が、その H⁰ を
元の raw 主完備化の H⁰ へ、標準 A 作用のまま比較する。
最後に `principalCompletionAdicAlgEquiv` の Raw 線形性で元の CP へ移す。
f=1 では j(dP) の単元性を標準射で CP へ移すため、全モニック入力を処理できる。
BS Rem 7.15（著者版 p.62）の p ねじれなしへの帰着と異なる、元の実源による補足計算である。

### 完了時の分類と受渡し

対象8ファイルの hpR 付き公開宣言を現在のファイルと照合した。
A1-a が既に削除・差替えした旧公開名も、上の17宣言の一覧の無条件版を正本とする。
単に証明から消せるだけの (a) はなく、正則性入力を射影性・被約性・有界ねじれ・
元の実完備化純性で代替した (b) が本系列の成果である。

- 17 の分冪構造・分冪公式・分冪射・普遍性：本節冒頭の正確な `_of_unconditional` 一覧。
  元の環・指定イデアル・係数作用・任意宇宙の標的を保持する。
- `powerRootPrismMonicRaw_p_mul_injective` と `powerRootPrismMonicRaw_pAdic_regular_pair`：
  今回の同名 `_of_unconditional` 版へ置換でき、hf 以外の仮定は追加しない。
- `powerRootPrismMonicRaw_pdCompletion_generator_regular`：
  `powerRootPrismMonicRaw_pdCompletion_generator_regular_of_monic_unconditional`。
- `powerRootPrismMonic_pdCompletion_prime_regular`：
  `powerRootPrismMonic_pdCompletion_prime_regular_of_unconditional`。
  後二つも f=1 を含む同じ H、同じ標準射であり、正次数は不要。
- H/dH の p 完全忠実平坦性と H の (p,d) 完全平坦性・標準剰余の忠実平坦性：
  既述の `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional`、
  `powerRootPrismMonicCompletion_pair_completelyFlat_of_unconditional`、
  `powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat_of_unconditional`。
  これらは元から必要な正次数を保持し、A1-d の仮定は解消済み。

(c) として元の強い署名を残す正確な旧名は次の8個である。

1. `perfectPrism_generator_modPrime_regular`
2. `perfectPrismVarpiLift_modPrime_regular`
3. `powerRootPrismGenerator_modPrime_regular`
4. `powerRootPrismFirstModPrimeRelation_regular`
5. `powerRootPrismMonicFirstModPrime_generator_regular`
6. `powerRootPrismMonicFinite_all_regular`
7. `powerRootPrismMonicRaw_mod_prime_generator_regular`
8. `powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular`

1–3 の d または varpi の mod p 正則性は、既証明の同値で hpR と同じ強さである。
4 は任意の非モニック f まで量化する旧型であり、d=p,f=0 の場合には初期関係が mod p で零となる。
原典のモニック設定では `powerRootPrismFirstModPrimeRelation_regular_of_monic_unconditional` が
hpR なしに供給済み。5–8 も mod p の分母正則性や H/dH の p 正則性という強い結論を含む。
非零な標数 p の perfectoid 基底まで許す一般の設定では成立しない。
原典 Rem 7.15（著者版 p.62）の計算は p ねじれなしへの基底変更後にこれらを使う。
従ってその帰着後なら hpR を供給できるが、一般の R=A/(d) 自体で自動的に成り立つ理由はない。
この違いを無条件化や新たな引用で隠していない。

`PowerRootMonicPDFlat` の二つの同名 hpR は `(p:R)=0` であり、p 正則性ではない。
任意 R に対する元の標数条件は残す。実係数 Rv では
`perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional` が自動供給し、
`powerRootMonicDPPresentation_free_of_unconditional` と
`powerRootMonicDPPresentation_faithfullyFlat_of_unconditional` が原典で使う形を満たす。

既存定理の差替えは依頼どおり A1-a の担当とし、この系列は新規無条件版の供給で完了する。
主定理、引用件数、BS Thm 1.17(1)、Cor 8.12 は変更していない。

### A1-d への受渡し（受領済みの記録）

依頼された初期係数段の受渡しの正確な型・API は、既存の同名節（A1-d 節内）に保存されている。
本担当節にも、受領と仮定解消の最終状態を明記する。
P,E,dP,a は上記の元の対象、`L₀ := PowerRootUnaryFreeDeltaRing A p hp`、
`Q := L₀ ⧸ Ideal.span {(p:L₀), MvPolynomial.C dP}`、
`Qinit := P ⧸ deltaDivisionFirstBaseIdeal (p:=p) dP a`、`R₀ := A/(p,d)` とする。
比較する通常のモニック無限根商は
`PowerRootPolynomialQuotient R₀ p hp (f.map (Ideal.Quotient.mk (Ideal.span {(p:A), W.generator})))`。
Qinit の通常商比較と `powerRootPolynomialQuotient_faithfullyFlat`、
`deltaAdjoinDivisionResidue_moduleFaithfullyFlat`、`Module.FaithfullyFlat.trans` を合成するのが受渡しの第一段。
A1-d の配置先は `Andre/Unconditional/InitialCoefficient/` で、このディレクトリは編集していない。

A1-b が受け取る `InitialCoefficient.sourceResidueH0_faithfullyFlat` の型は、
完全 prism W、hW、f、hf、hdeg に対して正確に次の結論である。

```lean
let R₀ := A ⧸ Ideal.span {(p : A), W.generator}
Module.FaithfullyFlat R₀
  ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
    ((boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), W.generator}))).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj)
```

`InitialCoefficient.rawResidue_faithfullyFlat` とともに受領済みであり、
その依存は今回の専用監査の型・値の推移的走査でも検査する。
途中の明示仮定を最終公開型に残していない。

### 最終検証と完了判定

`MonicRootedExtension` と専用監査の全 import 対象のビルドは `set -o pipefail` 付きで
4663 jobs、終了コード0。`scripts/audit_andre_unconditional.lean` は終了コード0で、
218 公開宣言の `assert_no_sorry`・`#print axioms` と新規12宣言の `#check` を実行し、
型・値の49,858依存宣言を走査した。許可公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
担当の Lean ファイル・監査・計画節の差分を確認し、新しい sorry・axiom・引用がないことを確認した。

対象8ファイルの旧 hpR の使用箇所は (b)・(c) と別の標数条件へ分類済み。
(b) の17分冪宣言、元の H と標準剰余への接続、raw p 正則性、通常 p 完備化の正則対は、
元の対象と標準係数作用を保持する無条件版で供給済み。
(c) の強い中間主張は一般の perfectoid 基底では偽なので無条件化しない。
原典の p ねじれなしへの帰着後の使用範囲を明記した。
A1-d の受領済み成果を使い、依頼された鎖の未証明仮定を最終公開型に残していない。
以上により A1-b の新規無条件版供給は完了。既存名の差替え・集約への公開・他系列との最終合流は、
依頼どおり別担当の作業である。


## A1-c：係数表記の照合

2026-10-17。BS Rem 7.15（著者版 p.62）と E1.25・E1.55・E1.56 の補足。
成果は `BhattScholze/Andre/VarpiComparison/` の新規ファイルに分離した。
既存の André ファイル、他担当の記録、主定理と引用入力は変更していない。
未採用の `bs-clmst-citation-elimination.md` は根拠にしない。

### 判定条件の修正と一般補題

通常商 M/ϖ の平坦性だけでは p 完全平坦性を判定できない。
非零の正則非単元 ϖ に対する M=R/(ϖ) では商は自由だが Tor₁ が残る。
利用者の了承に従い、逆方向の判定には基底 R と M 上の ϖ 正則性を明示した。
完全平坦性の定義は変更していない。

以下の公開名の namespace は `SerrePositivity.BhattScholze.Andre.VarpiComparison`。
`Flatness.lean` は、任意の可換環 R、v,c:R、n>0、hspan:(vⁿ)=(c) に対して次を証明する。
perfectoid 性を不要とする一般形であり、原典には c=p、n=p として適用する。
`span_power_eq_of_unit` が vⁿ=u·c（u:Rˣ）から hspan を供給する。

```lean
completelyFlat_iff : IsCompletelyFlat (Ideal.span {c}) M ↔
  IsCompletelyFlat (Ideal.span {v}) M
completelyFaithfullyFlat_iff : IsCompletelyFaithfullyFlat (Ideal.span {c}) M ↔
  IsCompletelyFaithfullyFlat (Ideal.span {v}) M
```

基底と M 上の v 正則性の下で、通常商 `AdicReduction (Ideal.span {v}) M` について
`completelyFlat_iff_flat_reduction` と
`completelyFaithfullyFlat_iff_faithfullyFlat_reduction` がそれぞれ平坦・忠実平坦判定を与える。
`algebraQuotient_faithfullyFlat` は c 完全忠実平坦な任意の R 代数 T に対して
`Module.FaithfullyFlat (R ⧸ Ideal.span {v}) (T ⧸ (Ideal.span {v}).map (algebraMap R T))`
を与える。この順方向には基底・T の正則性も完備性も不要。

### pd 係数底変換と原典の Frobenius 表記

R=A/(d)、x=φ_A⁻¹(d)、ϖ=x mod d とする。既存の実装の係数環は A/p であり、
R/p とは異なる。原典本文は p ねじれなしの場合へ帰着した後、φ*_A(T/ϖ) を扱っている。
この区別と Frobenius 変更を省略しない。
D_B(f) を B 上の無限根環の f(Y₀) に対する `PrincipalDPPresentation` と書く。

| 係数の比較 | 公開名・既存結果との対応 |
| --- | --- |
| 任意の S から S/(c) | `powerRootPDTensorQuotientEquiv`：S/(c)⊗_S D_S(f) ≃ D_{S/(c)}(f mod c)。全標準分冪生成元の一致も証明 |
| R/p から R/ϖ | `PrimeReduction.lean` の `primePDTensorVarpiEquiv`：R/ϖ⊗_{R/p} D_{R/p}(f mod p) ≃ D_{R/ϖ}(f mod ϖ)。二重商の自然係数作用を使用 |
| 既存の A/p 表示から R/ϖ | `perfectPrismPDTensorVarpiEquiv`：R/ϖ⊗_{A/p} PowerRootCoefficientPDEnvelope p f ≃ D_{R/ϖ}(f)。`perfectPrismVarpiPDEnvelopeEquiv` を全元でテンソル比較へ接続 |
| 実分冪構造 | `perfectPrismPDTensorVarpiDividedPowers` と全次数の生成元公式。`perfectPrismPDTensorVarpi_isDPMorphism` は自然な includeRight が全元で分冪を保つことを証明。既存の正則係数商の分冪射を再利用 |
| R/ϖ 上の基底計算 | 既存の `perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient` と `powerRootMonicDPPresentation_faithfullyFlat` に接続 |

通常の pd 表示環の底変換同型は正則性・モニック性を要求しない。
既存の実分冪構造と分冪射には、元の構成と同じ hpR とモニック性を明記する。

### 同じ候補 T の公開照合定理

`Candidate.lean` は E1.55–56 の元の raw 包・実完備化・分母商 T と自然な基底射を保持する。
f'=φ_A⁻¹(f)、Rv=R/ϖ、Tv=T/ϖ、Nv=Rv[Y^{1/p^∞}]、zv=f'(Y₀)、Qv=Nv/(zvᵖ) とする。
`hodgeTateVarpiPDAlgEquiv` は Tv≃ₐ[Rv]D_{Rv}(f')。
`hodgeTateVarpiPowerQuotientAlgebra` はこの同型を用いた Qv 作用を固定する。

`hodgeTate_coefficient_comparison W hW f hpR hf hdeg` は、
hpR:p の R 上の正則性、hf:f.Monic、hdeg:0<f.natDegree の下で、
次の全結論を一つの定理で与える（環・作用の let は上記の既存構成で固定）。

```lean
(IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
  Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
  IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
  Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv)
```

完全忠実平坦性の逆向きは、通常剰余の忠実平坦性と基底・候補の ϖ 正則性から導く。
原典の φ_A 引戻しを消して f と f' を同一視せず、prismatic envelope の全体同定や
ind-syntomic 性そのものの証明とは数えない。主定理・引用件数への影響はない。

### 検証

`lake build SerrePositivity.BhattScholze.Andre.VarpiComparison.Audit` が4147ジョブで成功。
専用 `Audit.lean` は新規29公開宣言を `assert_no_sorry` で検査し、
生成宣言を含む新規5モジュールの100宣言の推移的公理を検査した。
全て標準三公理 `propext`、`Classical.choice`、`Quot.sound` の範囲にあり、sorry 非依存。
一般判定・代数商・自然分冪射・R/p 底変換・候補集約の `#print axioms` も標準三公理のみ。

### E1.72／A1-a 原典の順序の完備入力環と試験射（2026-10-17）

本節は A1-a の追記。原典の R⟨Y^(1/p^∞)⟩/(f) を、通常の無限根多項式環を
p 完備化してからモニック関係で割る環として接続した。
A1-b の raw 包の正則性・完全忠実平坦性、A1-c の係数照合には立ち入らず、
既存 hpR 付き定理、並列担当の新規ファイルと記録節は変更していない。

以下はすべて名前空間 `SerrePositivity.BhattScholze.Andre` 内の新規公開宣言。
記載の略記を展開すると正確な型となる。係数環の非零性は要求しない。

#### 全冪商で正則な主入力による商の完備性（4 宣言）

`Andre/PrimeAdicCompletionPrincipalQuotient.lean`。
(R : Type u) [CommRing R]、p : ℕ、C=AdicCompletion (Ideal.span {(p : R)}) R、
j=algebraMap R C とする。

- `isAdicComplete_principal_quotient_of_regular_powers` は (a g : R)、
  [IsAdicComplete (Ideal.span {a}) R] と
  hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {a^n})
    (Ideal.Quotient.mk (Ideal.span {a^n}) g) の下で、
  `IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a}) (R ⧸ Ideal.span {g})`。
  p はこの宣言の引数ではない。
- `primeAdicCompletion_isAdicComplete R p` は
  `IsAdicComplete (Ideal.span {(p : C)}) C`。
- `primeAdicCompletion_regular_mod_power R p (g : R) (n : ℕ)` は、
  hg : IsSMulRegular (R ⧸ Ideal.span {(p : R)^n})
    (Ideal.Quotient.mk (Ideal.span {(p : R)^n}) g) の下で、
  `IsSMulRegular (C ⧸ Ideal.span {(p : C)^n})
    (Ideal.Quotient.mk (Ideal.span {(p : C)^n}) (j g))`。
- `primeAdicCompletion_principal_quotient_isAdicComplete R p (g : R)` は、
  hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R)^n})
    (Ideal.Quotient.mk (Ideal.span {(p : R)^n}) g) の下で、
  `IsAdicComplete (Ideal.span {(p : C ⧸ Ideal.span {j g})}) (C ⧸ Ideal.span {j g})`。

各冪商での g の正則性から a^n∣g*x ⇒ a^n∣x を直接得る。
乗法写像の逆像のフィルトレーション比較の k=0 を供給し、
既存 `isAdicComplete_quotient_range_of_uniform_filtration_bound` を使う。
従来の正則対の経路と異なり、a 自体の正則性は不要。
完備化への移送には既存 `adicCompletionPowQuotientEquiv` とその係数公式を再利用する。

#### 任意の係数主商と全 p 冪商でのモニック正則性（7 宣言）

`Andre/PowerRootPolynomialModScalar.lean`。
(A : Type u) [CommRing A]、p : ℕ、hp : 0 < p、a : A、
P=PowerRootPolynomial A p hp、R=A ⧸ Ideal.span {a}、Pbar=PowerRootPolynomial R p hp、
bar=Ideal.Quotient.mk (Ideal.span {a}) とする。

- `powerRootPolynomialModScalarMap A p hp a : P →+* Pbar`。
- `powerRootPolynomialModScalarMap_surjective A p hp a` は
  `Function.Surjective (powerRootPolynomialModScalarMap A p hp a)`。
- `powerRootPolynomialModScalarMap_ker A p hp a` は
  `RingHom.ker (powerRootPolynomialModScalarMap A p hp a) = Ideal.span {algebraMap A P a}`。
- `powerRootPolynomialModScalarEquiv A p hp a :
    (P ⧸ Ideal.span {algebraMap A P a}) ≃+* Pbar`。
- `powerRootPolynomialModScalarEquiv_mk A p hp a (x : P)` は
  `powerRootPolynomialModScalarEquiv A p hp a (Ideal.Quotient.mk _ x) =
    powerRootPolynomialModScalarMap A p hp a x`。
- `powerRootPolynomial_monic_mod_scalar_regular A p hp a (f : Polynomial A) (hf : f.Monic)` は
  `IsSMulRegular (P ⧸ Ideal.span {algebraMap A P a})
    (Ideal.Quotient.mk (Ideal.span {algebraMap A P a}) (powerRootPolynomialBaseMap A p hp f))`。
- `powerRootPolynomial_monic_mod_prime_power_regular A p hp (f : Polynomial A)
    (hf : f.Monic) (n : ℕ)` は
  `IsSMulRegular (P ⧸ Ideal.span {(p : P)^n})
    (Ideal.Quotient.mk (Ideal.span {(p : P)^n}) (powerRootPolynomialBaseMap A p hp f))`。
  この最後の宣言に a は引数として残らない。

指数を定める p と係数商の元 a を分離し、既存 mod p 比較の係数ごとの核計算を一般化した。
同じ番号の根変数を保ち、係数主商上のモニック性・既存の平坦性による正則性を移す。

#### 完備化と主商の交換同型（3 宣言）

`Andre/PrimeAdicCompletionQuotientExchange.lean`。
(R : Type u) [CommRing R]、p : ℕ、g : R、
hg : ∀ n : ℕ, IsSMulRegular (R ⧸ Ideal.span {(p : R)^n})
  (Ideal.Quotient.mk (Ideal.span {(p : R)^n}) g) を明示引数とする。
C と j は最初の節と同じ、S=R ⧸ Ideal.span {g}、q=Ideal.Quotient.mk (Ideal.span {g})、
CS=AdicCompletion (Ideal.span {(p : S)}) S、jS=algebraMap S CS、
Z=C ⧸ Ideal.span {j g}、qC=Ideal.Quotient.mk (Ideal.span {j g}) とする。

```lean
-- exists_primeAdicCompletionQuotientEquiv R p g hg
∃ e : Z ≃+* CS, e.toRingHom.comp (qC.comp j) = jS.comp q
-- primeAdicCompletionQuotientEquiv R p g hg
Z ≃+* CS
-- primeAdicCompletionQuotientEquiv_coeff R p g hg (x : R)
primeAdicCompletionQuotientEquiv R p g hg (qC (j x)) = jS (q x)
```

両側が p 完備であることから、通常の主商と完備化の普遍性で往復射を作る。
一意性で両合成が恒等射であることを示す。p 自体の正則性・有界ねじれ・素数性は不要。

#### 原典の順序のモニック完備入力環（4 宣言）

`Andre/PowerRootMonicCompletedInput.lean`。
{R : Type u} [CommRing R]、p : ℕ、hp : 0 < p、f : Polynomial R とする。
P=PowerRootPolynomial R p hp、z=powerRootPolynomialBaseMap R p hp f、
CP=AdicCompletion (Ideal.span {(p : P)}) P、jP=algebraMap P CP、
S₀=PowerRootEquationQuotient p hp f、CS=AdicCompletion (Ideal.span {(p : S₀)}) S₀。

```lean
PowerRootMonicCompletedInput p hp f : Type u := CP ⧸ Ideal.span {jP z}
-- powerRootMonicCompletedInputEquiv p hp f (hf : f.Monic)
PowerRootMonicCompletedInput p hp f ≃+* CS
-- powerRootMonicCompletedInputEquiv_coeff p hp f (hf : f.Monic) (x : P)
powerRootMonicCompletedInputEquiv p hp f hf
  (Ideal.Quotient.mk (Ideal.span {jP z}) (jP x)) =
    algebraMap S₀ CS (Ideal.Quotient.mk (Ideal.span {z}) x)
-- powerRootMonicCompletedInput_isAdicComplete p hp f (hf : f.Monic)
IsAdicComplete (Ideal.span {(p : PowerRootMonicCompletedInput p hp f)})
  (PowerRootMonicCompletedInput p hp f)
```

モニック性から全 p 冪商の正則性を内部で供給する。正次数・係数環の p 正則性・
有界ねじれ・完備性は不要。全ての元を保つ係数公式には各根変数の像も含まれる。
これにより E1.71 で未完了だった、通常の方程式商を先に完備化する環と
原典の順序の R⟨Y^(1/p^∞)⟩/(f) の同定を、この入力環について解消した。

#### 原典の順序の入力射から有界試験 prism への普遍性（1 宣言）

`Andre/PowerRootPrismMonicOriginalCompletedInput.lean` の
`existsUnique_powerRootPrismMonicCompletionHom_of_original_completed_input`。
完全 prism W : OrientedPrism p A、hW : W.deltaStructure.IsPerfect、f : Polynomial A、
hf : f.Monic を固定する。p は素数。P、E、dP、a、L、jL、H、uL、DH は E1.71 と同じ
元の raw 実完備化のデータを使う。
R=A ⧸ W.ideal、fR=f.map (Ideal.Quotient.mk W.ideal)、PR=PowerRootPolynomial R p hp、
CR=AdicCompletion (Ideal.span {(p : PR)}) PR、zR=powerRootPolynomialBaseMap R p hp fR、
SI=PowerRootMonicCompletedInput p hp fR とする。
lS:PR→+*SI は CR の主商射と algebraMap PR CR の合成。
引数は {B : Type u} [CommRing B]、Q : OrientedPrism p B、
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0、
k : OrientedPrism.Hom W Q、η : SI →+* B ⧸ Q.ideal、
hη : (η.comp lS).comp (algebraMap R PR)=k.quotientMap。
H の環構造 `pdCompletionCommRing L p (jL dP)` を let で導入した後の結論は

```lean
∃! F : H →+* B,
  DH.IsDeltaHom Q.deltaStructure F ∧
    F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k.toRingHom ∧
      ∀ n, Ideal.Quotient.mk Q.ideal
        (F (uL (jL (powerRootPolynomialVariable A p hp n)))) =
          η (lS (powerRootPolynomialVariable R p hp n))
```

である。入力環の交換同型の逆に沿って η を移し、全根の係数公式を使って
既存の完備入力からの普遍性を適用する。追加の hpR・正次数は不要。

BS Rem 7.15（著者版 p.62）の完備入力環の接続について、原典とは異なる
全冪商の正則性・一様なフィルトレーション比較・通常の主商と完備化の普遍性を使ったことを
docstring に明記した。これは入力環 S の接続と H からの試験射の一意性であり、
H 自体の prism 性、S→H/d の標準射と完全な入力作用を含む絶対 envelope の初期性は未完了。
A1-b の生成元正則性の成果、A1-c の係数表記の最終照合と合流する。
A1-a 全体の完成とは数えず、既存 hpR 付き定理は成果到着まで差し替えていない。

検証：新規 5 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4574 jobs）。新規 19 公開宣言の `assert_no_sorry` と専用監査は終了コード 0。
生成宣言を含む 7307 宣言の推移的公理依存は標準 3 公理のみ。
新規 19 公開宣言の正確な型を `#check` で確認した（終了コード 0）。

### 第二の区切り：元の A 上の実残余比較

`0418adfe` の最初の検証区切りに続き、次の新規4ファイルで元の A 作用へ接続した。
既存 Andre/ ファイルは変更していない。

- `Unconditional/FreeCoefficientSquare.lean`：自由 A 代数 S 上の射影モデルを A に制限し、
  A/(I) 還元と S/(IS) 還元の係数制限を比較する。自由性は一般補題の instance であり、
  今回の S=無限根自由 δ 環については A 自由性を内部供給する。
- `Unconditional/PowerRootCoefficientReduction.lean`：元の二因子導来テンソルの
  実自由 δ 源上での係数還元と、作用を β で制限した元の raw 残余商の single を比較する。
- `Unconditional/PowerRootQuotientDerived.lean`：源商の全射性で H⁰ の線形比較を
  実商環 Q=L₀/(p,dP) の作用へ降下し、実商環上での single 比較を構成する。
- `Unconditional/PowerRootAResidue.lean`：A のイデアル (p,d) の拡張と L₀ の (p,dP) を同定し、
  上の自由代数の正方形比較により、元の A/(p,d) に沿う実導来還元を同じ raw 残余商へ戻す。

`PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f` は、
元の自由 δ 射 α=deltaDivisionSourceMap E dP、評価射 β=deltaDivisionSourceEval E a の
二つの実スカラー加群の導来テンソルを、元の A 係数射に沿って制限した対象である。
`powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional W hW f hf` は
この実対象の A/(p,d) 導来還元と、実商環 Q の自然な作用を A/(p,d) に制限した
元の raw (p,d) 残余商の single との同型を与える。
`powerRootPrismMonicSourceCoefficientPDResidue_homology_isZero_of_unconditional`
は全非零整数次数の消滅を供給する。hpR・Tor 消滅・追加の平坦性を呼出し側に要求しない。

この第二の区切りでは、まだ同じ残余商の元の A/(p,d) 上の忠実平坦性を供給していない。
次は P の初期係数商 P/(p,dP,a) を (A/(p,d)) 上の通常モニック無限根商と比較して
忠実平坦性を得て、既存の raw 残余商の初期係数商上の忠実平坦性と合成する。
その後、実逐次完備化単位と生成元冪商の有界ねじれによる純性を接続し、
元の H と dH の分母正則性、H/dH の p 完全忠実平坦性、H の (p,d) 完全平坦性へ進む。
これらの最終接続は未完了であり、目標を達成扱いにしない。

第二の区切りの検証：`MonicRootedExtension` と全新規対象を含むビルドは
4586ジョブで成功した。拡張した `scripts/audit_andre_unconditional.lean` は
65 公開宣言をすべて `assert_no_sorry` で検査し、45,431 宣言の依存走査も
終了コード0で成功した。標準三公理以外の公理・sorry 依存はない。
本節に明示した最終接続は依然として未完了であり、目標は継続する。


## A1-d：初期係数商の忠実平坦性

2026-10-17。A1-b の「A1-d への受渡し」は着手時には未記載だったため、
「無条件の弱い入力と残る接続」と「第二の区切り」から次の目標型を先に固定する。
完全 prism W : OrientedPrism p A、hW、モニック f : Polynomial A、0<f.natDegree に対し、
P=PowerRootPolynomial A p hp、E=powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure、
dP=algebraMap A P W.generator、a=powerRootPrismMonicUnaryFamily f、
R=A/(p,W.generator)、J=deltaDivisionFirstBaseIdeal dP a、Qinit=P/J、
Res=DeltaAdjoinDivisionResidue E dP a とする。

新規 namespace `SerrePositivity.BhattScholze.Andre.InitialCoefficient` に、
R 上の自然な作用を保持する
`initialCoefficientAlgEquiv : Qinit ≃ₐ[R] PowerRootPolynomialQuotient R p hp (f.map (Ideal.Quotient.mk _))`、
`initialCoefficient_faithfullyFlat : Module.FaithfullyFlat R Qinit`、
`rawResidueBase_faithfullyFlat : Module.FaithfullyFlat R Res` を公開する。
最後の作用は A1-b の実係数射 κ と実 raw 残余射の合成との一致を照合する。
一般の `deltaAdjoinDivisionResidue_moduleFaithfullyFlat` を初期商上の既存結果として用いる。
hpR、係数商の非零性、追加の平坦性・Tor 消滅は仮定しない。
既存の André ファイルと他担当の節は編集せず、成果と専用監査は
`Andre/Unconditional/InitialCoefficient/` の新規ファイルだけに置く。

### A1-d の実装と受渡しの検証

着手後に A1-b が正式な受渡しを追記した。最終公開型はその二つの型に合わせた。
`Comparison.lean` は d を任意の係数元として、初期イデアルの表示、
全 P 代表元を保つ環同型、元の A 係数の保存、R 代数同型、自由性・忠実平坦性を証明する。
忠実平坦性の非零枝だけでモニック次数保存を用い、零係数商は別枝で処理する。

`RawResidue.lean` は完全 prism から P と自由 δ 源 L₀ の p 正則性、
ghost 単射性、δ(dP) の単元を内部供給する。
`deltaAdjoinDivisionResidue_moduleFaithfullyFlat` と初期商の忠実平坦性を
`Module.FaithfullyFlat.trans` で合成する。係数射について

```lean
rawResidueBaseMap W hW f =
  (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).comp
    (powerRootSourceQuotientCoefficientMap_of_unconditional W)
```

を全 A 代表元で証明する `rawResidueBaseMap_eq_source` を公開した。
この等式による、元の Res の元を保つ線形同型で、受渡し指定の作用に忠実平坦性を移す。
初期商 Qinit と自由 δ 源商 Q₀=L₀/(p,C dP) は別の環のまま保持する。

共通引数は `{A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]`、
`W : OrientedPrism p A`、`hW : W.deltaStructure.IsPerfect`、`f : Polynomial A`、
`hf : f.Monic`、`hdeg : 0 < f.natDegree`。名前空間は上記 `Andre.InitialCoefficient`。
κ と ψ をそれぞれ受渡しの指定係数射・実 raw 残余射とすると、公開型は次のとおり。

```lean
rawResidue_faithfullyFlat W hW f hf hdeg :
  letI := ψ.toAlgebra
  letI : Module Q₀ Res := Algebra.toModule
  Module.FaithfullyFlat R ((ModuleCat.restrictScalars κ).obj (ModuleCat.of Q₀ Res))

sourceResidueH0_faithfullyFlat W hW f hf hdeg :
  Module.FaithfullyFlat R
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj)
```

後者は既存の `powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional` への移送。
hpR、係数商の非零性、追加の Tor 消滅や平坦性を仮定しない。
A1-b の正式な二つの結論型を専用監査内に固定し、追加仮定なしに適用できることを検査した。

検証：`lake build SerrePositivity.BhattScholze.Andre.Unconditional.InitialCoefficient.Audit`
は4110ジョブで成功。新規20公開宣言は全件 `assert_no_sorry` が成功し、
生成宣言を含む新規2モジュールの51宣言の推移的公理も標準三公理だけと確認した。
初期商・合成係数射の一致・raw 残余商・H⁰ の `#print axioms` は
`propext`、`Classical.choice`、`Quot.sound` のみ。新しい sorry・axiom・引用はない。
既存ファイル・他担当の節・主定理の引用入力を変更せず、担当ファイルだけを個別保存する。
この成果は鎖の第一段の受渡しであり、実逐次完備化後の正則性・完全忠実平坦性や
A1-c2 の hpR 除去を完成扱いにしない。

### A1-d への受渡し

2026-10-17 のユーザー指示による分担変更。鎖の最初の段を A1-d に渡す。
A1-d の配置先は `SerrePositivity/BhattScholze/Andre/Unconditional/InitialCoefficient/` 以下。
A1-b はこのディレクトリのファイルを編集しない。
A1-d の専用監査は別ファイル `scripts/audit_andre_initial_coefficient.lean` を推奨する。
A1-b は以下の H⁰ 忠実平坦性を明示仮定にして純性と H 側の接続を進め、成果受領後に解消する。
主定理、BS Thm 1.17(1)、Cor 8.12、既存 Andre/ のファイルは担当外。

**元の対象と自然な作用。** 以下の型は
`SerrePositivity.BhattScholze.Andre` の既存名を使う。
`P=PowerRootPolynomial A p hp`、`E=powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure`、
`dP=algebraMap A P W.generator`、`a=powerRootPrismMonicUnaryFamily (p:=p) f`、
`L₀=PowerRootUnaryFreeDeltaRing A p hp`、`Q=L₀/(p,C dP)` である。
初期係数商は `Qinit=P ⧸ deltaDivisionFirstBaseIdeal (p:=p) dP a = P/(p,dP,a)`。
Qinit と実自由 δ 源の商 Q を混同しない。
`κ=powerRootSourceQuotientCoefficientMap_of_unconditional W` と
`powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f` によって、
既存の実 raw 残余商の自然な R=A/(p,d) 作用を固定する。

**A1-d の証明対象（提案名は名前空間 `Andre.InitialCoefficient` 内）。**
共通の暗黙引数は `{A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]`。
`open CategoryTheory` と `attribute [local instance] HasDerivedCategory.standard` の下で述べる。
以下は結論までの正確な Lean の型であり、型全体は `/tmp/a1d-interface.lean` で検査する。

```lean
theorem rawResidue_faithfullyFlat (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  let hp := Nat.Prime.pos (Fact.out : p.Prime)
  let P := PowerRootPolynomial A p hp
  let E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
  let dP := algebraMap A P W.generator
  let a := powerRootPrismMonicUnaryFamily (p := p) f
  let L₀ := PowerRootUnaryFreeDeltaRing A p hp
  let Q := L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.C dP}
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  let Res := DeltaAdjoinDivisionResidue E dP a
  let κ := powerRootSourceQuotientCoefficientMap_of_unconditional W
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q Res := Algebra.toModule
  Module.FaithfullyFlat R ((ModuleCat.restrictScalars κ).obj (ModuleCat.of Q Res))

```

さらに既存の H⁰ 比較を使い、A1-b が直接受け取る次の型を供給する。

```lean
theorem sourceResidueH0_faithfullyFlat (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  Module.FaithfullyFlat R
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj)

```

**通常商の比較と合成に使う既存 API。**

- 通常のモニック無限根商は
  `PowerRootPolynomialQuotient (A ⧸ Ideal.span {(p:A), W.generator}) p hp
    (f.map (Ideal.Quotient.mk (Ideal.span {(p:A), W.generator})))`。
  主イデアル表示との照合は `powerRootPolynomialQuotient_ideal`。
- 係数商との交換は `powerRootCoefficientIdealQuotientEquiv`、同 `_mk`、
  `powerRootCoefficientIdealQuotientMap_coeff` と同 `_baseMap`。
  二重商は `DoubleQuot.quotQuotEquivQuotSup`。
- 通常商の自由性・忠実平坦性は `powerRootPolynomialQuotient_free`、
  `powerRootPolynomialQuotient_faithfullyFlat`。正次数 hdeg は後者にのみ必要。
- 初期係数商上の raw 残余商の係数射・忠実平坦性は
  `deltaAdjoinDivisionResidueBaseMap`、同 `_mk`、
  `deltaAdjoinDivisionResidueBaseAlgebra`、`deltaAdjoinDivisionResidue_moduleFaithfullyFlat`。
  hpP、hpL、ghost 単射性、δ(dP) の単元は完全 prism から内部供給する。
  `powerRootPolynomial_primeRegular`、`powerRootPrismGenerator_isDistinguished`、
  `witt_ghostMap_injective_of_mul_prime_injective` が既存 API。
- 合成は `Module.FaithfullyFlat.trans`。新しく構成する R→Qinit→Res の係数射が、
  上の κ と実源商の係数射の合成と全 A 代表元上で一致することを確認する。
  環同型だけで自然な R 作用を取り替えてはならない。
- raw 残余商から実還元 H⁰ への移送は
  `powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional W hW f hf`。
  これは既存の `Unconditional/PowerRootAResidue.lean` にあり、A1-b の検証済み成果。

**既に途中で作った下書き。** 分担変更前の未検証の二つの草稿を
`/tmp/andre-a1d-drafts/PowerRootInitialCoefficient.lean` と
`/tmp/andre-a1d-drafts/PowerRootRawResidueFlat.lean` に退避した。
これらはビルド済み成果ではなく、必要なら参考として使える。
A1-b は以後この最初の段を実装せず、A1-d の成果で上記の明示仮定を解消する。

### A1-d／受渡し指定型の独立再監査（2026-10-17）

受渡し後の確認中に、同じ InitialCoefficient の完成版が並行コミットされたことを確認した。
初期係数商の比較は `8e0a2a6a`、指定作用の raw 残余商と H⁰ は `18de67e0`、
専用 Lean 監査モジュールは `998e512d`。これらの保存済み証明は書き換えず再利用した。
こちらで作成した未検証の二つの重複草稿は `/tmp/a1d-current-attempt/` に退避し、
リポジトリには残していない。

指定された実行入口 `scripts/audit_andre_initial_coefficient.lean` を独立に追加した。
本スクリプトは上の二つの受渡し型を let と局所作用も含め全文で固定し、
`rawResidue_faithfullyFlat` と `sourceResidueH0_faithfullyFlat` を追加仮定なしに適用する。
公開20宣言の `assert_no_sorry` に加え、実装二モジュールの生成宣言を含む全宣言に
`collectAxioms` を実行し、標準三公理以外をエラーとして拒否する。

検証はすべて `set -o pipefail` の下で終了コードを確認した。
`lake build SerrePositivity.BhattScholze.Andre.Unconditional.InitialCoefficient.Audit`
は4110ジョブで終了コード0。
`lake env lean scripts/audit_andre_initial_coefficient.lean` も終了コード0。
独立スクリプトで列挙された141宣言の推移的公理は標準三公理のみで、
指定二定理の実依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
元の係数射の一致は `rawResidueBaseMap_eq_source` で保持されている。

この再監査の変更は独立スクリプトと本節だけ。元の Andre/・他レーンのファイル・
ルート集約は変更しない。実逐次完備化後の純性・正則性・完全忠実平坦性、
A1-b 側での仮定解消、A1-c2 の hpR 除去はこの第一段の完成と区別する。

### E1.73／A1-a 標準入力作用と可換図式による普遍性（2026-10-17）

本節は A1-a の追記。通常の入力環から元の H/d への標準射を無条件に構成し、
その作用を保つ試験射の一意存在を証明した。原典の完備入力作用に対しては、
H/d の通常の p 完備性を明示引数 hT にして同じ可換図式の普遍性を接続した。
既存 hpR 付き定理と並列担当のファイル・記録節は変更していない。

以下の公開名はすべて `SerrePositivity.BhattScholze.Andre` 内。
共通の入力は {A : Type u} [CommRing A]、{p : ℕ} [Fact p.Prime]、
W : OrientedPrism p A、hW : W.deltaStructure.IsPerfect、f : Polynomial A。
P、E、dP、a、L、jL、H、uL、DH は E1.72 と同じ元の raw 実完備化のデータ。
dH=uL (jL dP)、T=H ⧸ Ideal.span {dH}、qH=Ideal.Quotient.mk (Ideal.span {dH})、
R=A ⧸ W.ideal、fR=f.map (Ideal.Quotient.mk W.ideal)、
S₀=PowerRootEquationQuotient p hp fR、cS と rS は S₀ の標準係数射・根列、
φ₀=powerRootPrismMonicHodgeTateBaseMap W hW f、baseH=powerRootPrismMonicCompletionBaseMap W hW f。
以下で H と T を使う型の先頭には、コードと同じく
`let := pdCompletionCommRing L p (jL dP)` が付く。

#### 通常の標準入力射（6 公開宣言）

新規 `Andre/PowerRootPrismMonicStandardEquationInput.lean`。

```lean
-- powerRootPrismMonicHodgeTateRoots W hW f (n : ℕ)
T
-- powerRootPrismMonicHodgeTateRoots_pow W hW f n
powerRootPrismMonicHodgeTateRoots W hW f (n+1)^p =
  powerRootPrismMonicHodgeTateRoots W hW f n
-- powerRootPrismMonicHodgeTateRoots_eval W hW f
fR.eval₂ φ₀ (powerRootPrismMonicHodgeTateRoots W hW f 0) = 0
-- powerRootPrismMonicEquationInputMap W hW f
S₀ →+* T
-- powerRootPrismMonicEquationInputMap_coeff W hW f
(powerRootPrismMonicEquationInputMap W hW f).comp cS = φ₀
-- powerRootPrismMonicEquationInputMap_root W hW f n
powerRootPrismMonicEquationInputMap W hW f (rS n) =
  powerRootPrismMonicHodgeTateRoots W hW f n
```

標準根の定義は qH (uL (jL Y_n))。全根の互換性を環射で写し、
既存の raw 関係による第零根の評価定理を再利用する。
方程式商の普遍性で input₀=powerRootPrismMonicEquationInputMap W hW f を構成する。
モニック性・正次数・hpR・T の通常の p 完備性はいずれも不要。

#### H の剰余射と通常入力作用を保つ普遍性（5 公開宣言）

新規 `Andre/PowerRootPrismMonicEquationInputSquare.lean`。
{B : Type u} [CommRing B]、Q : OrientedPrism p B、k : OrientedPrism.Hom W Q、
qB=Ideal.Quotient.mk Q.ideal を固定する。

- `powerRootPrismMonicReductionMap W hW f Q k` の型は
  `(F : H →+* B) → F.comp baseH=k.toRingHom → T →+* B ⧸ Q.ideal`。
- `powerRootPrismMonicReductionMap_mk W hW f Q k` は
  ∀ (F : H →+* B) (hF : F.comp baseH=k.toRingHom) (x : H),
  `powerRootPrismMonicReductionMap W hW f Q k F hF (qH x)=qB (F x)`。
- `powerRootPrismMonicReductionMap_coeff W hW f Q k` は同じ F、hF に対し
  `(powerRootPrismMonicReductionMap W hW f Q k F hF).comp φ₀=k.quotientMap`。
- `powerRootPrismMonicEquationInputSquare_iff_roots` は η:S₀→+*B⧸Q.ideal、
  hη:η.comp cS=k.quotientMap、同じ F、hF の下で

```lean
(powerRootPrismMonicReductionMap W hW f Q k F hF).comp input₀ = η ↔
  ∀ n, qB (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (rS n)
```

を証明する。δ 条件を課さない任意の基底保存環射について成り立つ。
`existsUnique_powerRootPrismMonicHom_preserving_equation_input` はさらに
hB:∃N:ℕ,∀n:ℕ,∀x:B⧸Q.ideal,(p:B⧸Q.ideal)^n*x=0→(p:B⧸Q.ideal)^N*x=0
の下で、正確に

```lean
∃! F : H →+* B, DH.IsDeltaHom Q.deltaStructure F ∧
  ∃ hF : F.comp baseH=k.toRingHom,
    (powerRootPrismMonicReductionMap W hW f Q k F hF).comp input₀ = η
```

を証明する。基底生成元の像が Q.ideal に入ることから剰余射を降下する。
係数と全根による方程式商の外延性で、根保存から入力環全体の可換性へ移す。
H 自体の prism 性・T の通常の p 完備性・モニック性・正次数・hpR は不要。

#### 原典の完備入力環の標準作用（4 公開宣言、条件付き）

新規 `Andre/PowerRootPrismMonicStandardCompletedInput.lean`。
PR=PowerRootPolynomial R p hp、CR=AdicCompletion (Ideal.span {(p:PR)}) PR、
zR=powerRootPolynomialBaseMap R p hp fR、SI=PowerRootMonicCompletedInput p hp fR、
lS:PR→+*SI は CR の主商射と algebraMap PR CR の合成。
hf:f.Monic の下で、先頭の H の環構造の let の後に
**hT:IsAdicComplete (Ideal.span {(p:T)}) T を明示引数として要求する**。

```lean
-- powerRootPrismMonicOriginalInputMap W hW f hf hT
SI →+* T
-- powerRootPrismMonicOriginalInputMap_poly W hW f hf (x : PR) hT
powerRootPrismMonicOriginalInputMap W hW f hf hT (lS x) =
  input₀ (Ideal.Quotient.mk (Ideal.span {zR}) x)
-- powerRootPrismMonicOriginalInputMap_coeff W hW f hf hT
(powerRootPrismMonicOriginalInputMap W hW f hf hT).comp
  (lS.comp (algebraMap R PR)) = φ₀
-- powerRootPrismMonicOriginalInputMap_root W hW f hf (n : ℕ) hT
powerRootPrismMonicOriginalInputMap W hW f hf hT (lS (powerRootPolynomialVariable R p hp n)) =
  powerRootPrismMonicHodgeTateRoots W hW f n
```

input₀ を通常の商の p 完備化へ一意に延長し、E1.72 のモニック交換同型を合成する。
hT を hpR で供給したとはみなさず、無条件の完備入力作用の完成とは数えない。

#### 完備入力射の外延性（1 公開定理）

新規 `Andre/PowerRootMonicCompletedInputExt.lean` の
`powerRootMonicCompletedInput_ringHom_ext`。
この定理だけは一般の {R:Type u} [CommRing R]、p:ℕ、hp:0<p、f:Polynomial R、
{B:Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p:B)}) B] を使い、宇宙は独立。
P=PowerRootPolynomial R p hp、SI=PowerRootMonicCompletedInput p hp f、
lS は通常の無限根多項式環から SI への標準射として、
F G:SI→+*B、hc:(F.comp lS).comp (algebraMap R P)=(G.comp lS).comp (algebraMap R P)、
hr:∀n,F(lS Y_n)=G(lS Y_n) の下で F=G を証明する。
主商・p 完備化・無限根多項式環の外延性を順に適用する。モニック性は不要。

#### 原典の完備入力作用を保つ普遍性（2 公開定理、条件付き）

新規 `Andre/PowerRootPrismMonicOriginalInputSquare.lean`。
共通の W、hW、f、Q、k、hf と、有界性 hB、
η:SI→+*B⧸Q.ideal、hη:(η.comp lS).comp (algebraMap R PR)=k.quotientMap を使う。
H の環構造の let の後に hT を明示的に量化する。
`powerRootPrismMonicOriginalInputSquare_iff_roots` は同じ F、hF の下で

```lean
(powerRootPrismMonicReductionMap W hW f Q k F hF).comp
  (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η ↔
    ∀ n, qB (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (lS Y_n)
```

を証明する。`existsUnique_powerRootPrismMonicHom_preserving_original_input` は

```lean
∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
∃! F : H →+* B, DH.IsDeltaHom Q.deltaStructure F ∧
  ∃ hF : F.comp baseH=k.toRingHom,
    (powerRootPrismMonicReductionMap W hW f Q k F hF).comp
      (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η
```

を証明する。有界試験 prism の商の通常の p 完備性を内部で供給し、
全根の保存から原典の完備入力環全体の可換性を結論する。

BS Rem 7.15（著者版 p.62）への接続として、原典とは異なる具体的な入力射、
通常の主商と完備化の普遍性、全根による外延性を用いたことを docstring に記録した。
未完了は hT の無条件の供給、H の生成元正則性と prism 化、prism の射としての
初期性の合流、A1-c の最終係数照合との接続。条件付きの完備入力の成果を
A1-a 全体の完成とは数えない。既存 hpR 付き定理は差し替えていない。

検証：新規 5 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4579 jobs）。新規 18 公開宣言の `assert_no_sorry` と専用監査は終了コード 0。
生成宣言を含む 7631 宣言の推移的公理依存は標準 3 公理のみ。
新規 18 公開宣言の正確な型を `#check` で確認した（終了コード 0）。

### E1.74／A1-a 元の H の条件付き prism 化と prism 射の普遍性（2026-10-17）

本節は A1-a の追記。E1.73 の δ 環射による普遍性を、元の H と元の標準分母を使う
prism 射の一意存在へ接続した。生成元正則性と有界ねじれは明示仮定のまま残す。
既存 hpR 付き定理、並列担当のファイル・記録節は変更していない。

以下の名前はすべて名前空間 `SerrePositivity.BhattScholze.Andre` 内。
共通の入力は {A : Type u} [CommRing A]、{p : ℕ} [Fact p.Prime]、
W : OrientedPrism p A、hW : W.deltaStructure.IsPerfect、f : Polynomial A。
P、E、dP、a、L、jL、H、uL、DH、R、fR、PR、SI、lS、baseH、T は E1.73 と同じ。
dH=uL (jL dP)。以下で H、T を使う型の先頭にはコードと同じく
`let := pdCompletionCommRing L p (jL dP)` が付く。

#### 元の H の条件付き prism 構造（6 公開宣言）

新規 `Andre/PowerRootPrismMonicRegularSource.lean`。
`powerRootPrismMonicCompletionPrismOfRegular W hW f` の正確な型は

```lean
let := pdCompletionCommRing L p (jL dP)
IsSMulRegular H dH → OrientedPrism p H
```

である。以下、hreg:IsSMulRegular H dH、
PH=powerRootPrismMonicCompletionPrismOfRegular W hW f hreg と書く。

- `powerRootPrismMonicCompletionPrismOfRegular_generator W hW f hreg` は `PH.generator=dH`。
- `powerRootPrismMonicCompletionPrismOfRegular_deltaStructure W hW f hreg` は
  `PH.deltaStructure=DH`。
- `powerRootPrismMonicCompletionPrismOfRegular_ideal W hW f hreg` は
  `PH.ideal=Ideal.span {dH}`。
- `powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg : OrientedPrism.Hom W PH`。
- `powerRootPrismMonicCompletionPrismBaseHomOfRegular_toRingHom W hW f hreg` は
  `(powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg).toRingHom=baseH`。

既存の標準 δ 射で distinguished 性を移し、実完備化の p と dH の導来完備性を供給する。
正則性だけを hreg として渡して `OrientedPrism.ofDistinguished` を使う。
元の環・δ 構造・生成元・商 H/dH を変更しない。モニック性・正次数・hpR は不要。
hreg を無条件に証明したとは主張せず、既存の hpR 付き構成も差し替えていない。

#### 基底を保つ δ 射と prism 射（4 公開宣言）

新規 `Andre/PowerRootPrismMonicSourcePrismUniversal.lean`。
{B : Type u} [CommRing B]、Q : OrientedPrism p B、k : OrientedPrism.Hom W Q を固定する。
basePH=powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg とする。

- `powerRootPrismMonicSourceHomOfDelta W hW f Q k` は、H の環構造の let の後に
  (hreg:IsSMulRegular H dH)、(F:H→+*B)、hδ:DH.IsDeltaHom Q.deltaStructure F、
  hF:F.comp baseH=k.toRingHom を受け取り、`OrientedPrism.Hom PH Q` を返す。
- `powerRootPrismMonicSourceHomOfDelta_toRingHom W hW f Q k hreg F hδ hF` は
  `(powerRootPrismMonicSourceHomOfDelta W hW f Q k hreg F hδ hF).toRingHom=F`。
- `powerRootPrismMonicSourceHomOfDelta_comp_base W hW f Q k hreg F hδ hF` は
  `(powerRootPrismMonicSourceHomOfDelta W hW f Q k hreg F hδ hF).comp basePH=k`。
- `powerRootPrismMonicSourceHom_quotientMap W hW f Q k` は、同じ hreg、
  G:OrientedPrism.Hom PH Q、hG:G.toRingHom.comp baseH=k.toRingHom に対し
  `G.quotientMap=powerRootPrismMonicReductionMap W hW f Q k G.toRingHom hG`。

F(dH)=k(W.generator)∈Q.ideal からイデアル保存性を供給する。
prism 射の剰余射を E1.73 の実際の H/dH の剰余射へ同定し、標準入力作用を保持する。

#### 原典の完備入力作用を保つ prism 射の一意存在（1 公開定理、条件付き）

同ファイルの `existsUnique_powerRootPrismMonicPrismHom_preserving_original_input`。
W、hW、f、Q、k の後の明示引数は
hf:f.Monic、
hB:∃N:ℕ,∀n:ℕ,∀x:B⧸Q.ideal,(p:B⧸Q.ideal)^n*x=0→(p:B⧸Q.ideal)^N*x=0、
η:SI→+*B⧸Q.ideal、hη:(η.comp lS).comp (algebraMap R PR)=k.quotientMap。
H の環構造の let の後の正確な結論は

```lean
∀ (hreg : IsSMulRegular H dH)
  (hT : IsAdicComplete (Ideal.span {(p : T)}) T),
∃! G : OrientedPrism.Hom
    (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q,
  G.comp (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg) = k ∧
    G.quotientMap.comp (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η
```

である。入力作用を保つ一意な δ 射を prism 射として構成し、台の環射による外延性で一意性を移す。
源は既存の実 H⁰ と同一であり、ねじれ除去商や別の完備化へ変更していない。

#### 有界な源の剰余から通常の完備性を供給する合流点（2 公開定理）

同ファイルの `powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f` は、
H の環構造の let の後に、正確に

```lean
(∃ N : ℕ, ∀ n : ℕ, ∀ x : T, (p : T)^n*x=0 → (p : T)^N*x=0) →
  IsAdicComplete (Ideal.span {(p : T)}) T
```

を証明する。この定理に Q、k、hf、hreg は引数として残らない。
実 H⁰ の導来 p 完備性を通常の主商 T に移し、有界ねじれ比較を使う。
p 正則性を要求せず、T の有界 p ねじれから hT を供給する。

`existsUnique_powerRootPrismMonicPrismHom_of_bounded_source` の引数は上の
prism 射の一意存在と同じ W、hW、f、Q、k、hf、hB、η、hη。
H の環構造の let の後の正確な結論は

```lean
∀ (hreg : IsSMulRegular H dH)
  (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
    (p : T)^n*x=0 → (p : T)^N*x=0),
let hT := powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f hBound
∃! G : OrientedPrism.Hom
    (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q,
  G.comp (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg) = k ∧
    G.quotientMap.comp (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η
```

である。hT を独立の仮定とせず、剰余 T の有界 p ねじれから内部で供給する。
ただし hreg と hBound を無条件に証明したとはみなさない。

BS Rem 7.15（著者版 p.62）の源と普遍性に対し、原典とは異なる raw 実完備化の構造、
具体的な標準入力作用、通常の主商の剰余射、有界ねじれ比較による経路を docstring に記録した。
最小の残る接続点は、**同じ H の標準分母像の正則性**と**同じ T=H/dH の有界 p ねじれ**。
これらの無条件の供給と A1-c の最終係数照合との合流が残る。
条件付きの prism 構造・初期性を、絶対 prismatic envelope 全体の同定完了とは数えない。

検証：新規 2 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4581 jobs）。新規 13 公開宣言の `assert_no_sorry` と専用監査は終了コード 0。
生成宣言を含む 7785 宣言の推移的公理依存は標準 3 公理のみ。
新規 13 公開宣言の正確な型を `#check` で確認した（終了コード 0）。

### E1.75／A1-a 入力作用を持つ有界 prism の圏と条件付き初期性（2026-10-17）

本節は A1-a の追記。E1.74 の基底・完備入力作用を保つ prism 射の一意存在を、
固定基底 W 上の有界な向き付き入力 prism の圏の IsInitial へ接続した。
hreg と hBound は引き続き明示仮定であり、原典の絶対 prismatic site との比較も未完了。
既存 hpR 付き定理と並列担当のファイル・記録節は変更していない。

以下の公開名はすべて名前空間 `SerrePositivity.BhattScholze.Andre` 内。

#### 入力作用を持つ有界 prism の圏（10 公開宣言）

新規 `Andre/BoundedPrismInputCategory.lean`。
{p : ℕ} [Fact p.Prime]、{A S : Type u} [CommRing A] [CommRing S]、
W : OrientedPrism p A、c : A ⧸ W.ideal →+* S を固定する。

`BoundedPrismInput W c : Type (u+1)` の正確なフィールドは次の通り。

```lean
ring : CommRingCat.{u}
prism : OrientedPrism p ring
base : OrientedPrism.Hom W prism
input : S →+* ring ⧸ prism.ideal
input_base : input.comp c = base.quotientMap
bounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : ring ⧸ prism.ideal,
  (p : ring ⧸ prism.ideal)^n*x=0 → (p : ring ⧸ prism.ideal)^N*x=0
```

X,Y : BoundedPrismInput W c に対し、`BoundedPrismInput.Hom X Y` は
`OrientedPrism.Hom X.prism Y.prism` を親構造とし、以下を追加する。

```lean
over_base : toHom.comp X.base = Y.base
over_input : toHom.quotientMap.comp X.input = Y.input
```

親構造の射は orientation の厳密な保存を要求せず、δ 構造とイデアルの保存を要求する。
その他の公開宣言の正確な型は、同じ W,c の下で以下。

- `BoundedPrismInput.hom_ext`：{f g : BoundedPrismInput.Hom X Y}、
  h:f.toHom=g.toHom の下で f=g。
- `BoundedPrismInput.homId (X : BoundedPrismInput W c) : BoundedPrismInput.Hom X X`。
- `BoundedPrismInput.homComp`：{X Y Z : BoundedPrismInput W c}、
  f:Hom X Y、g:Hom Y Z を受け取り `Hom X Z` を返す。
- `BoundedPrismInput.category : Category.{u} (BoundedPrismInput W c)`。
- `BoundedPrismInput.id_toHom X`：`(𝟙 X : X ⟶ X).toHom=OrientedPrism.Hom.id X.prism`。
- `BoundedPrismInput.comp_toHom`：f:X⟶Y、g:Y⟶Z の下で
  `(f ≫ g).toHom=g.toHom.comp f.toHom`。
- `BoundedPrismInput.isInitialOfPrismUniversal`：X:BoundedPrismInput W c と

```lean
h : ∀ Y : BoundedPrismInput W c,
  ∃! f : OrientedPrism.Hom X.prism Y.prism,
    f.comp X.base=Y.base ∧ f.quotientMap.comp X.input=Y.input
```

を受け取り `IsInitial X` を返す。
- `BoundedPrismInput.isoRingEquiv`：{X Y : BoundedPrismInput W c} と e:X≅Y を受け取り
  `X.ring ≃+* Y.ring` を返す。

恒等射・合成の可換性は既存の prism 射・標準商射の合成公式で示す。
入力作用を持つ射の外延性で圏の法則と初期性を構成する。
この圏の定義自体は、任意の入力環に初期対象が存在するという仮定・引用ではない。
環同型は圏の同型の往復射から取り出すため、基底・入力・δ 構造の保存も元の射に保持される。

#### 元の H の対象・初期性・比較同型（5 公開宣言、条件付き）

新規 `Andre/PowerRootPrismMonicEnvelopeInitial.lean`。
共通の入力は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic。
P、E、dP、a、L、jL、H、uL、DH、R、fR、PR、SI、lS、baseH、T は E1.74 と同じ。
cS=lS.comp (algebraMap R PR) : R→+*SI とする。
H を使う型の先頭には `let := pdCompletionCommRing L p (jL dP)` が付く。
以下の二つの仮定の型は共通。

```lean
hreg : IsSMulRegular H (uL (jL dP))
hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
  (p : T)^n*x=0 → (p : T)^N*x=0
```

公開宣言の正確な型・結論は次の通り。

```lean
-- powerRootPrismMonicSourceInputObject W hW f hf hreg hBound
BoundedPrismInput W cS
-- powerRootPrismMonicSourceInput_isInitial W hW f hf hreg hBound
IsInitial (powerRootPrismMonicSourceInputObject W hW f hf hreg hBound)
```

元の H を台環として、同じ標準分母像の prism、同じ基底射、同じ完備入力射を束ねる。
入力の基底保存性は E1.73 の係数公式を再利用し、対象の有界性は hBound をそのまま供給する。
任意の比較対象 Y について、その Q=Y.prism、k=Y.base、hB=Y.bounded、η=Y.input、
hη=Y.input_base を E1.74 の prism 射の一意存在に渡す。

任意の Z : BoundedPrismInput W cS、hZ : IsInitial Z に対して、さらに

```lean
-- powerRootPrismMonicSourceInputIso W hW f hf hreg hBound Z hZ
powerRootPrismMonicSourceInputObject W hW f hf hreg hBound ≅ Z
-- powerRootPrismMonicSourceEnvelopeRingEquiv W hW f hf hreg hBound Z hZ
H ≃+* Z.ring
-- powerRootPrismMonicSourceEnvelopeRingEquiv_base_coeff W hW f hf (a₀ : A)
--   hreg hBound Z hZ
powerRootPrismMonicSourceEnvelopeRingEquiv W hW f hf hreg hBound Z hZ
  (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base.toRingHom a₀
```

を公開した。IsInitial は初期射を持つデータであり、存在を仮定する新しい axiom ではない。
比較同型は二つの初期対象の一意な同型から得る。元の H の環同型と全係数像の保存も明示した。

BS Rem 7.15（著者版 p.62）の envelope 比較への接続として、原典とは異なる
入力作用を持つ有界な向き付き prism の明示的な圏、元の実完備化、初期対象の同型を使う経路を
各 docstring に記録した。これは固定基底 W・向き付き対象の圏での条件付き初期性である。
原典の絶対 prismatic site 全体との比較を暗黙に済ませたとは主張しない。
未完了は hreg・hBound の無条件の供給、その圏との比較、A1-c の最終係数照合との合流。
これらが残るため、絶対 prismatic envelope 全体の同定完了とは数えない。

検証：新規 2 ファイルの対象ビルドと集約ビルドは終了コード 0
（集約 4583 jobs）。新規 15 公開宣言と主要射影 9 件の `assert_no_sorry`、専用監査は終了コード 0。
生成宣言を含む 7934 宣言の推移的公理依存は標準 3 公理のみ。
同じ 24 件の正確な型を `#check` で確認した（終了コード 0）。

### E1.76／A1-a 一般有界標的での完全源の剛性と基底条件の回復（2026-10-17）

本節は A1-a の追記。固定基底を持つ入力圏から原典の絶対 prismatic site への比較について、
原典 BS Lemma 4.8（著者版 pp.38–39）が必要であることを本文で再確認した。
原典 Remark 4.7（p.38）は絶対 site の対象を有界 prism としている。
既存 `existsUnique_perfectPrismHomLift` は標的も完全な場合に限られ、一般標的への存在には使わない。
今回は一般の有界標的に対する一意性を新しく証明し、射の基底条件の回復へ接続した。
持上げの存在や Lemma 4.8 全体を証明済みとはしない。新しい引用は追加していない。

公開名はすべて名前空間 `SerrePositivity.BhattScholze.Andre` 内。
既存 hpR 付き定理と並列担当のファイル・記録節は変更していない。

#### イデアル冪による環射の剛性（3 公開定理）

新規 `Andre/PerfectSourceAdicRigidity.lean`。
{B:Type v} [CommRing B] を固定する。p:ℕ はこのファイルでは任意の自然数。
I:Ideal B、hp:(p:B)∈I とする。

- `geomSum_mem_ideal_of_natCast_mem p I hp (x y:B) (hxy:x-y∈I)` の結論は
  `(∑ i ∈ Finset.range p, x^i*y^(p-1-i))∈I`。
- `pow_sub_pow_mem_ideal_succ p I hp x y hxy (n:ℕ) (hn:x-y∈I^n)` の結論は
  `x^p-y^p∈I^(n+1)`。
- `ringHom_ext_of_pow_add_natCast_mul` の正確な型は、

```lean
(p : ℕ) {A : Type u} [CommRing A]
(hA : ∀ a : A, ∃ b c : A, a = b^p + (p:A)*c)
(I : Ideal B) (hp : (p:B)∈I) [IsHausdorff I B]
(F G : A →+* B)
(hFG : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp G) : F = G
```

である。最初の幾何和は商で p*y^(p-1) となるため I に入る。
冪差の因数分解により差の所属冪を一段深くし、源の p 冪近似 a=b^p+p*c で帰納する。
分離性で全冪の差を消す。素数性・p 正則性・δ 構造はこの一般補題には不要。

#### 完全源から有界 prism への一意性（2 公開定理）

新規 `Andre/PerfectPrismBoundedTargetRigidity.lean`。
{p:ℕ} [Fact p.Prime]、{A:Type u} {B:Type v} [CommRing A] [CommRing B]。
宇宙 u,v は独立。Q:OrientedPrism p B と

```lean
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p:B⧸Q.ideal)^n*x=0 → (p:B⧸Q.ideal)^N*x=0
```

を使う。
`ringHom_ext_to_boundedPrism_of_perfect_source` は
D:DeltaStructure p A、hD:D.IsPerfect、Q、hB、F G:A→+*B、
hFG:(Ideal.Quotient.mk Q.ideal).comp F=(Ideal.Quotient.mk Q.ideal).comp G
を受け取り **F=G** を証明する。
射 F,G に δ 保存性を要求しない。完全な源では Frobenius 持上げの全射性により
各 a を b^p+p*δ(b) と書ける。標的の (p,d) 古典的完備性による分離性と、
Q.ideal⊂(p,d) を使って一般の環射の剛性を適用する。

`perfectPrismHom_ext_to_bounded_target` は
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、Q、hB、
F G:OrientedPrism.Hom W Q、hFG:F.quotientMap=G.quotientMap
を受け取り **F=G** を証明する。
標的 Q の完全性・p 正則性は不要。これは BS Lemma 4.8 の一意性部分を
絶対 site の一般有界対象に対して証明したもので、存在部分は含まない。

#### 入力作用からの基底保存性（3 公開宣言）

新規 `Andre/BoundedPrismInputRigidity.lean`。
このファイルの公開名の namespace は `SerrePositivity.BhattScholze.Andre.BoundedPrismInput`。
{p:ℕ} [Fact p.Prime]、{A S:Type u} [CommRing A] [CommRing S]、
{W:OrientedPrism p A}、{c:A⧸W.ideal→+*S}、hW:W.deltaStructure.IsPerfect、
X Y:BoundedPrismInput W c を使う。

- `prismHom_over_base_of_input hW X Y` は f:OrientedPrism.Hom X.prism Y.prism と
  hf:f.quotientMap.comp X.input=Y.input の下で **f.comp X.base=Y.base** を証明する。
- `homOfInput hW X Y f hf : X ⟶ Y` は、基底保存性を追加引数にせず入力圏の射を構成する。
- `homEquivInputPreserving hW X Y` の正確な型は

```lean
(X ⟶ Y) ≃ { f : OrientedPrism.Hom X.prism Y.prism //
  f.quotientMap.comp X.input = Y.input }
```

である。入力の可換性を c で制限すると二つの基底 prism 射の商射が一致するため、
上の一般有界標的への完全源の剛性で基底保存性を回復する。
既に基底を持つ対象間では、射の追加の基底保存条件を除けることを示した。
基底を持たない任意の絶対入力対象に基底射が存在することまでは主張しない。

原典 Lemma 4.8 の証明は変形理論で環射を持ち上げ、逆 Frobenius 極限で δ 保存性を確認する。
今回はその一意性部分を、幾何和・イデアル冪・分離性による異なる直接証明で得た。
この相違を docstring に明記し、Rem 7.15（著者版 p.62）の入力圏への用途も記録した。
Lemma 4.8 の一般有界標的での存在部分、向き付き対象と原典の対象との比較、
同じ H の hreg・同じ T の hBound の供給、A1-c の係数照合との合流は未完了。
絶対 prismatic envelope 全体の同定完了とは数えない。

検証：新規3モジュールの対象ビルドと集約ビルド（4586 jobs）は、`set -o pipefail` 付きで終了コード0を確認した。専用監査の8公開宣言の `assert_no_sorry` が通り、対象モジュールの7947宣言について推移的に標準3公理のみと確認した（終了コード0）。別ファイルの8本の `#check` でも上記の引数・型を確認した。

### E1.77／A1-a 一般有界 prism の台環の古典的 p 完備性（2026-10-17）

本節は A1-a の追記。BS Lemma 4.8（著者版 pp.38–39）の基底射の存在への準備として、
有界 prism の台環に古典的 p 完備性を供給した。新規ファイルは
`Andre/BoundedPrismPrimeComplete.lean`。公開名はすべて
`SerrePositivity.BhattScholze.Andre` 内。原典の変形理論による持上げとは異なり、
既存の差分作用による導来比較と (p,d) 分離性を使う。新たな引用は追加していない。

公開2定理の正確な型は以下。宇宙 u は任意。

```lean
isAdicComplete_of_isModuleComplete_of_isHausdorff
    (R : Type u) [CommRing R] (a : R)
    (h : DerivedCompletion.IsModuleComplete R a (ModuleCat.of R R))
    [IsHausdorff (Ideal.span {a}) R] :
    IsAdicComplete (Ideal.span {a}) R

boundedPrism_isAdicComplete_prime
    {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
    (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0) :
    IsAdicComplete (Ideal.span {(p : B)}) B
```

第一定理では導来完備性から差分作用の全単射性を得て、その全射性から前完備性を得る。
分離性と合わせれば古典的完備性となる。第二定理では `Q.complete_p` と
既存 `boundedPrism_isHausdorff_prime Q hB` を第一定理に渡す。
台環の p 正則性・有界 p ねじれ、標的の完全性は要求しない。

検証：対象ビルド（2737 jobs）と集約ビルド（4587 jobs）は `set -o pipefail` 付きで
終了コード0を確認した。公開2定理の `assert_no_sorry` が通り、専用監査は7949宣言を
推移的に標準3公理のみと確認して終了コード0。別ファイルの2本の `#check` で上記の型を確認した。

未完了：一般有界標的への基底射の存在・δ 保存性、向き付き対象と絶対 site の比較、
同じ源 H の生成元正則性と同じ商 T の有界性、A1-c の係数照合との合流。
本節だけで Lemma 4.8 全体や絶対 prismatic envelope の同定を完了とはしない。
A1-b・A1-c のファイル・記録節、既存 hpR 付き定理は変更していない。

### E1.78／A1-a 完全な源からの環射の δ 保存性（2026-10-17）

本節は A1-a の追記。新規 `Andre/PerfectSourceDeltaHom.lean` で、BS Lemma 4.8
（著者版 pp.38–39）の持上げた環射の δ 判定を証明した。原典の逆 Frobenius 極限とは異なり、
環射の剛性と W₂ の第1座標の差の導分を使う。環射の存在はまだ結論しない。
新しい引用・sorry・axiom は追加していない。公開名はすべて
`SerrePositivity.BhattScholze.Andre` 内。以下、宇宙 u,v は独立、
{p:ℕ} [Fact p.Prime]、{A:Type u} {B:Type v} [CommRing A] [CommRing B] を固定する。

公開4定理の正確な型は以下。

```lean
perfectSource_ringHom_map_frobenius
    (D : DeltaStructure p A) (hD : D.IsPerfect) (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) :
    E.frobeniusLift.comp f = f.comp D.frobeniusLift

wittTwoHom_ext_of_perfectSource_approximation
    (hA : ∀ a : A, ∃ b c : A, a = b^p + (p:A)*c)
    (f : A →+* B) (s t : A →+* WittTwo p B)
    (hs : (wittTwoProjection p B).comp s = f)
    (ht : (wittTwoProjection p B).comp t = f)
    (hghost : (wittTwoFrobenius p B).comp s = (wittTwoFrobenius p B).comp t) :
    s = t

perfectSource_ringHom_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) : D.IsDeltaHom E f

perfectSource_ringHom_isDeltaHom_to_boundedPrism
    (D : DeltaStructure p A) (hD : D.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0)
    (f : A →+* B) : D.IsDeltaHom Q.deltaStructure f
```

Frobenius との二つの合成は mod p で一致するため、E1.76 の p 冪近似の剛性で一致する。
二つの W₂ 射の第1座標の差 ε は加法的で p*ε(a)=0。
ghost が同じなので、ε はその共通 ghost 射に沿う導分となる。
ε(b^n)=n*g(b)^(n-1)*ε(b) と ε(p)=0 を使い、a=b^p+p*c から ε(a)=0 を得る。
これを `(wittTwoMap f).comp D.sectionHom` と `E.sectionHom.comp f` に適用する。
標的の p 正則性は不要で、有界 prism では E1.68 の p 分離性だけで適用できる。

未完了：商写像を持ち上げる環射の存在、向き付き対象と原典の絶対 site の比較、
同じ H の生成元正則性と同じ T の有界性、A1-c の係数照合との合流。
δ 保存性は本節で解消したが、Lemma 4.8 全体・絶対 prismatic envelope の同定完了とは数えない。
並列担当のファイル・記録節と既存 hpR 付き定理は変更していない。

検証：対象ビルド（2749 jobs）と集約ビルド（4588 jobs）は `set -o pipefail` 付きで終了コード0。公開4定理の `assert_no_sorry` と4本の `#check` は終了コード0。専用監査の結果は `André monic root audit passed: 7955 declarations, standard axioms only.`。私有補題もモジュール全宣言監査に含む。

### E1.79／A1-a 一般有界 prism の台環と商の tilt 比較（2026-10-17）

本節は A1-a の追記。新規 `Andre/BoundedPrismTiltQuotient.lean` に、一般有界 prism の
台環と prism 商の tilt 比較を追加した。BS Lemma 4.8（著者版 pp.38–39）の基底環射の存在を、
tilt 上の係数持上げと Fontaine 写像へ帰着するための準備である。原典の変形理論とは異なる
Teichmüller モノイド同型と互換根列の一意持上げによる経路。新引用は追加していない。

公開名はすべて `SerrePositivity.BhattScholze.Andre` 内。共通設定は
{B:Type u} [CommRing B]、{p:ℕ} [Fact p.Prime]、Q:OrientedPrism p B、
[Fact (¬ IsUnit (p:B))]、[Fact (¬ IsUnit (p:B⧸Q.ideal))]、および

```lean
hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0
```

とする。台環での p 非可逆性は商での非可逆性から従うが、標数の型クラスのため明示した。
標的の完全性・p 正則性は不要。公開3宣言の型は次のとおり。

```lean
boundedPrism_preTiltQuotient_bijective Q hB :
  Function.Bijective (Perfection.map p (modPMap p (Ideal.Quotient.mk Q.ideal)))

boundedPrism_preTiltQuotientEquiv Q hB :
  PreTilt B p ≃+* PreTilt (B ⧸ Q.ideal) p

boundedPrism_preTiltQuotientEquiv_coeff Q hB (x : PreTilt B p) (n : ℕ) :
  PreTilt.coeff n (boundedPrism_preTiltQuotientEquiv Q hB x) =
    modPMap p (Ideal.Quotient.mk Q.ideal) (PreTilt.coeff n x)
```

台環の p 完備性は E1.77、商の p 完備性は E1.68 から供給する。
両方の tilt を台環内の実互換根列と乗法的に同一視する。
既存 `existsUnique_boundedPrismCompatibleRootsLift` が実根列の全単射性を与え、
標準 tilt 環射の全単射性へ移せる。環構造の加法性は標準の `Perfection.map` が既に持つため、
Teichmüller の乗法同型に加法性を別途仮定していない。

未完了：tilt 係数持上げから Fontaine 写像を合成した基底環射の構成と商図式の確認、
零商の場合の統合、絶対 site の対象との比較、A1-b の正則性・有界性の結果と源の初期性の合流、
A1-c の係数照合との合流。本節の型は p 非可逆性を明示しており、条件なしの Lemma 4.8
全体を完成したとはしない。A1-b の成果 `84c99b11` の到着を確認したが、
今回の保存単位では既存 hpR 付き定理の差替え・並列担当ファイルの編集はしていない。

検証：対象ビルド（3095 jobs）と最終対象・集約ビルド（4589 jobs）は `set -o pipefail` 付きで終了コード0。公開3宣言の `assert_no_sorry` と3本の `#check` は終了コード0。専用監査は `André monic root audit passed: 7961 declarations, standard axioms only.`。

### E1.80／A1-a 元の H の prism 性と完備入力圏での初期性の合流（2026-10-17）

本節は A1-a の追記。A1-b の保存済み成果 `84c99b11` を受領し、新規
`Andre/PowerRootPrismMonicSourceInitiality.lean` で E1.74・E1.75 の二つの補助仮定を解消した。
BS Rem 7.15（著者版 p.62）の元の源 H を保持する。原典とは異なる実逐次完備化・
純性と明示的な入力圏による経路であり、新しい引用・sorry・axiom は追加していない。
並列担当のファイル・記録節は編集していない。

公開名はすべて `SerrePositivity.BhattScholze.Andre` 内。
共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、
hf:f.Monic、hdeg:0<f.natDegree である。以下の記号は元の定義そのもの。

```lean
hp := Nat.Prime.pos (Fact.out : p.Prime)
P := PowerRootPolynomial A p hp
E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
dP := algebraMap A P W.generator
a := powerRootPrismMonicUnaryFamily (p := p) f
L := DeltaAdjoinDivision E dP a
jL := deltaAdjoinDivisionMap E dP a
H := PDCompletionH0 L p (jL dP)
uL := pdCompletionUnit L p (jL dP)
dH := uL (jL dP)
T := H ⧸ Ideal.span {dH}
R := A ⧸ W.ideal
fR := f.map (Ideal.Quotient.mk W.ideal)
PR := PowerRootPolynomial R p hp
CR := AdicCompletion (Ideal.span {(p : PR)}) PR
zR := powerRootPolynomialBaseMap R p hp fR
SI := PowerRootMonicCompletedInput p hp fR
lS := (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})).comp (algebraMap PR CR)
cS := lS.comp (algebraMap R PR)
```

H の環構造は `pdCompletionCommRing L p (jL dP)`。
この let を必要な型の先頭に置く。公開6宣言の正確な型は次のとおり。

```lean
powerRootPrismMonicCompletionPrismOfMonicPositive W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  OrientedPrism p H

powerRootPrismMonicCompletionPrismOfMonicPositive_generator W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  (powerRootPrismMonicCompletionPrismOfMonicPositive W hW f hf hdeg).generator = dH

powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg :
  BoundedPrismInput W cS

powerRootPrismMonicSourceInput_isInitialOfMonicPositive W hW f hf hdeg :
  IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive W hW f hf hdeg
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) :
  let := pdCompletionCommRing L p (jL dP)
  H ≃+* Z.ring

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff W hW f hf hdeg
    (Z : BoundedPrismInput W cS) (hZ : IsInitial Z) (a₀ : A) :
  let := pdCompletionCommRing L p (jL dP)
  powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive W hW f hf hdeg Z hZ
    (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base.toRingHom a₀
```

A1-b の `powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional`
と `powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional` を既存の源構成へ渡す。
元の H の環・δ 構造・標準生成元・標準係数射と、完備してから f で割った SI の標準入力作用を
保持する。公開結果には hpR、hreg、hBound を仮定として残していない。
初期性比較先の hZ は初期対象同士の比較に必要な普遍性であり、源の構成の条件ではない。

この時点で正次数モニック入力について、同じ H の prism 性・同じ T の有界性と通常の p 完備性・
原典の順序の完備入力環 SI の作用・固定完全基底と向き付き対象の入力圏での初期性が合流した。
原典の絶対 site 全体との同定は未完了。一般有界対象への基底環射の存在と、
向き付き対象から一般 Cartier イデアルの対象への比較、A1-c の係数照合との合流が残る。

既存の hpR 付き公開名の差替えも未完了である。今回の新規定理は正次数を仮定する。
既存の生成元正則性定理は正次数を仮定しないため単純に型を置換できず、零次数モニック f=1 の
場合の処理が別途必要。また A1-b の実装は既存ファイルの係数作用の定義を import しているため、
旧名側で新ファイルを直接 import すると循環する。共有の係数定義を新規ファイルへ移すなど、
依存関係を確認してから正しい範囲の旧名を差し替える。元来偽となる mod p 正則性の中間主張は
無条件化しない。これらを旧名の差替えまで完了したとは数えない。

検証：対象ビルド（4390 jobs）と集約ビルド（4610 jobs）は `set -o pipefail` 付きで終了コード0。公開6宣言の `assert_no_sorry` と6本の `#check` は終了コード0。専用監査は `André monic root audit passed: 8046 declarations, standard axioms only.`。A1-b の受領結果への推移的公理依存もこの検査に含む。

### E1.81／A1-a 完全源から一般有界 prism への商射の一意持上げ（2026-10-17）

本節は A1-a の追記。新規 `Andre/PerfectPrismBoundedTargetLift.lean` で、
BS Lemma 4.8（著者版 pp.38–39）の向き付き有界標的での存在・一意性を証明した。
原典の変形理論と逆 Frobenius 極限は使わず、完全源の Witt 復元、tilt 比較、Fontaine 写像、
Witt 持上げの一意性、E1.78 の自動 δ 保存性を使う異なる経路。新しい引用は追加していない。

公開名は `SerrePositivity.BhattScholze.Andre` 内。共通設定は、独立な宇宙 u,v、
{p:ℕ} [Fact p.Prime]、{A:Type u} {B:Type v} [CommRing A] [CommRing B]。
公開2定理の正確な型は次のとおり。

```lean
existsUnique_perfectPrismRingHomLift_to_bounded
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal)

existsUnique_perfectPrismHomLift_to_bounded
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : OrientedPrism.Hom W Q, F.quotientMap = g
```

非零な標的商では、その p 完備性から p 非可逆性を証明する。台環 B と源 A での p 非可逆性は
商射と g へ写して供給するため、これらは公開定理の引数に残らない。
k=A/(p)、s:k→(B/Q.ideal)/(p) を g の標準 mod p 射とし、完全性で s を商の tilt へ持ち上げる。
E1.79 の tilt 比較の逆で台環の tilt へ戻し、Witt.map と Fontaine θ を合成する。
Witt 復元による A への同型を介して A→B を得る。商図式は mod p の座標計算と
`wittLift_unique` で確認する。零商なら Q.ideal=⊤ と生成元完備性から B も零となる。
従って標的の完全性・p 正則性・非零性・p 非可逆性は一切前提に残らない。
最後に自動 δ 保存性と商図式からのイデアル保存性により prism 射へまとめる。

解消した範囲：一般有界な向き付き標的での基底射の存在・一意性・δ 保存性。
これにより完備入力作用だけを持つ対象へ完全基底からの射を自動供給できる。
未完了は、その入力圏全体での源の初期性への接続、一般 Cartier イデアルを持つ向きなし
prism の扱い、A1-c の係数比較との合流、既存 hpR 付き公開名の差替え。
原典の絶対 prismatic envelope 全体の同定をこの2定理だけで完成とはしない。
並列担当のファイル・節は編集していない。

検証：対象ビルド（3121 jobs）と集約ビルド（4611 jobs）は `set -o pipefail` 付きで終了コード0。公開2定理の `assert_no_sorry` と2本の `#check` は終了コード0。専用監査は `André monic root audit passed: 8050 declarations, standard axioms only.`。私有補題もモジュール全宣言の監査に含む。

### E1.82／A1-a 基底射を指定しない絶対入力への源の普遍性（2026-10-17）

本節は A1-a の追記。新規 `Andre/PowerRootPrismMonicAbsoluteUniversal.lean` で、
原典の完備入力環 SI の作用だけから、元の源 H からの prism 射を一意に構成した。
BS Rem 7.15（著者版 p.62）の絶対 envelope の普遍性を、現在の向き付き対象で証明した。
原典の変形理論とは異なる E1.81 の tilt・Fontaine による基底持上げと実完備化を使う経路。
新しい引用・sorry・axiom は追加していない。

公開名は `SerrePositivity.BhattScholze.Andre.existsUnique_powerRootPrismMonicPrismHom_of_absolute_input`。
E1.80 の H、T、SI、cS の定義を保持する。共通引数は {A B:Type u} [CommRing A] [CommRing B]、
{p:ℕ} [Fact p.Prime]、W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、
f:Polynomial A、hf:f.Monic、hdeg:0<f.natDegree。正確な残りの型は次のとおり。

```lean
(Q : OrientedPrism p B)
(hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal)^n*x=0 → (p : B ⧸ Q.ideal)^N*x=0)
(η : SI →+* B ⧸ Q.ideal) :
let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
∃! G : OrientedPrism.Hom X.prism Q, G.quotientMap.comp X.input = η
```

源 X の台環は元の H、prism 生成元は dH、入力は元の標準完備入力射である。
η.comp cS を完全基底から Q への唯一の prism 射 k へ持ち上げる。
固定基底での既存の源の普遍性から射を構成する。
任意の入力保存射も完全基底からの商射の剛性により k を保つので、基底条件を仮定せず一意性が従う。
源の hreg・hBound・hT、標的の k とその可換図式、標的の完全性・p 正則性・非零性は
この公開定理の前提に一切残らない。

型の範囲は同じ宇宙 u の向き付き prism である。E1.81 の基底持上げは独立宇宙 u,v で成り立つが、
ここで再利用した源の普遍性は同じ宇宙で実装されているため、独立宇宙へ一般化済みとはしない。
一般 Cartier イデアルを持つ向きなし prism の扱いと、原典の絶対 prismatic site 全体の同定、
A1-c の係数照合との合流、既存 hpR 付き公開名の差替えは引き続き未完了。
並列担当のファイル・記録節は変更していない。

検証：対象ビルド（4409 jobs）と集約ビルド（4612 jobs）は `set -o pipefail` 付きで終了コード0。公開定理の `assert_no_sorry` と `#check` は終了コード0。専用監査は `André monic root audit passed: 8126 declarations, standard axioms only.`。

### E1.83／A1-a 旧公開名の hpR 差替え・集約検証で中断（2026-10-17）

本節は A1-a の未保存単位の記録。A1-b の `aa1d72fd` を受領した。
`Unconditional/PrimeReductionPurity.lean` のモニック入力全体に対する元の H の p 正則性と
標準分母像の正則性を使い、自分の既存公開名を差し替える変更を作業木に置いた。
既存の hf を維持し、正次数を追加せず hpR を除く変更である。
対象の公開名は `SerrePositivity.BhattScholze.Andre` 内の次の9宣言。

- `powerRootPrismMonicRaw_pdCompletion_generator_regular`
- `powerRootPrismMonic_pdCompletion_prime_regular`
- `powerRootPrismMonicCompletionPrism`
- `powerRootPrismMonicCompletionBaseMap_generator`
- `existsUnique_powerRootPrismMonicCompletionHom`
- `powerRootPrismMonicCompletionTorsionEquiv`
- `powerRootPrismMonicCompletionTorsionEquiv_coeff`
- `powerRootPrismMonicCompletionTorsionEquiv_isDeltaHom`
- `powerRootPrismMonicCompletionHom_generator`

raw の mod p 分母正則性、分母商の p 正則性など本質的な hpR を必要とする中間主張は変更していない。
標準分母像を使う後続の自分の呼出しも更新した。並列担当のファイルは編集していない。
BS Rem 7.15（著者版 p.62）と異なる実源の純性の経路を該当 docstring に記載した。

対象ビルドの終了コード0を確認したが、最後の対象・集約ビルドは終了コード1。
`PowerRootPrismMonicEquationInput.olean` の `no such file or directory (error code: 2)` による失敗であり、
確認時には同じ生成物が存在していた。並行ビルドの共有生成物の競合が疑われる。
依存先が並行作業で壊れた場合は回避せず止める指示に従い、ここで検証を停止した。
失敗した実行は `/tmp/andre-e183-aggregate.log`、終了済みセッション12874。
監査と9本の `#check` はまだ実行していない。型確認用ファイルは `/tmp/andre-e183-check.lean`。
本節・変更6ファイルはいずれも未コミットであり、旧名の差替え完了とは数えない。
次回は共有生成物の現在状態を再確認してから検証を再開する。

### A1-f への受渡し

2026-10-17 の最新指示により A1-e は起動せず、R1（残る hpR 付き公開名の差替え）は
A1-a が継続する。向きなし prism は A1-f が別チャットで担当する。
本節には A1-f が保つべき公開名だけを残す。

#### A1-f の定義ファイルと保存すべき公開名

定義ファイルは `Andre/BoundedPrismInputCategory.lean`。
namespace は `SerrePositivity.BhattScholze.Andre`。
`BoundedPrismInput W c` は台環、prism、base、input、
`input_base : input.comp c = base.quotientMap`、bounded を持つ。
A1-f は新規ファイルで同値を作り、次の既存名・型・標準作用を保つ。

- `BoundedPrismInput` と各フィールド、`BoundedPrismInput.Hom` と
  `toHom`・`over_base`・`over_input`。
- `BoundedPrismInput.category`、`hom_ext`、`homId`、`homComp`、`id_toHom`、`comp_toHom`、
  `isInitialOfPrismUniversal`、`isoRingEquiv`。
- `BoundedPrismInputRigidity.lean` の `BoundedPrismInput.prismHom_over_base_of_input`、
  `homOfInput`、`homEquivInputPreserving`。
- `BoundedPrismHomRigidity.lean` の `existsUnique_boundedPrismHom_generator_unit`、
  `boundedPrismHom_generator_span`、`boundedPrismHom_map_ideal_eq`。
  W の完全性から distinguished 性を供給し、base(d) の span が対象の prism イデアルに等しいことを使える。
- `PowerRootPrismMonicSourceInitiality.lean` の
  `powerRootPrismMonicCompletionPrismOfMonicPositive`、
  `powerRootPrismMonicSourceInputObjectOfMonicPositive`、
  `powerRootPrismMonicSourceInput_isInitialOfMonicPositive` と生成元・環同型・係数公式。
- E1.82 の `existsUnique_powerRootPrismMonicPrismHom_of_absolute_input`。
  完備してから f で割る `PowerRootMonicCompletedInput`、元の H、標準係数射・入力射を保持する。

A1-f は J=(d)B を使い、生成元を base(d) とする向きなし対象との同値と初期性の移送を公開する。
射には生成元の厳密な保存を追加せず、イデアル・入力作用・基底係数作用を保つ。
A1-a は既存定義を変更せず新規の最終合流から利用する。
一般 Cartier 対象・宇宙の範囲は同値の実際の型に従って記録し、定義だけで全 site と同定しない。

### E1.83 再検証／R1 旧9公開宣言の hpR 解消（2026-10-17）

最新のユーザー指示により、先の失敗は依存先の破損ではなく並行ビルドの共有 .olean 競合と確認した。
`ps -axo pid=,comm=,args=` で他レーンの lake build がない時点を確認し、同じ5対象と集約を再実行した。
`set -o pipefail` 付きで 4613 jobs、終了コード0。先の読込み失敗を回避する別構成は作っていない。
A1-e は起動せず R1 は本担当が続ける。受渡し節を A1-f が保つ公開名の項目だけに整理した。

変更した自分の既存ファイルは `PowerRootPrismMonicRawPairRegular`、`CompletionRegular`、
`CompletionPrism`、`CompletionUniversal`、`CompletionPairFlat`。
A1-b の `aa1d72fd` による任意モニック入力の正則性へ旧名を接続し、
hpR を除いた次の9公開宣言を確認した。namespace はすべて `SerrePositivity.BhattScholze.Andre`。
共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、W:OrientedPrism p A、
hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic。
E1.80 の P,E,dP,a,L,jL,H,uL,dH を使い、H の環構造を各型の先頭の
`let := pdCompletionCommRing L p (jL dP)` で供給する。追加の正次数仮定はない。

```lean
powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf :
  let dL := jL dP
  letI := pdCompletionCommRing L p dL
  IsSMulRegular H (pdCompletionUnit L p dL dL)

powerRootPrismMonic_pdCompletion_prime_regular W hW f hf :
  let := pdCompletionCommRing L p (jL dP)
  IsSMulRegular H (p : H)

powerRootPrismMonicCompletionPrism W hW f hf :
  let := pdCompletionCommRing L p (jL dP)
  OrientedPrism p H

powerRootPrismMonicCompletionBaseMap_generator W hW f hf :
  let := pdCompletionCommRing L p (jL dP)
  powerRootPrismMonicCompletionBaseMap W hW f W.generator =
    (powerRootPrismMonicCompletionPrism W hW f hf).generator

existsUnique_powerRootPrismMonicCompletionHom W hW f hf
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hg : E.IsDeltaHom Q.deltaStructure g) (hd : g dP = Q.generator)
    (ha : Q.generator ∣ g (powerRootMonicPDInput p f)) :
  let := pdCompletionCommRing L p (jL dP)
  ∃! F : H →+* B,
    (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
      Q.deltaStructure F ∧ F.comp (uL.comp jL) = g

powerRootPrismMonicCompletionTorsionEquiv W hW f hf :
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  H ≃+* DerivedDeltaDivisionCompletion E dP a

powerRootPrismMonicCompletionTorsionEquiv_coeff W hW f hf (r : P) :
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  powerRootPrismMonicCompletionTorsionEquiv W hW f hf (uL (jL r)) =
    derivedDeltaDivisionMap E dP a r

powerRootPrismMonicCompletionTorsionEquiv_isDeltaHom W hW f hf :
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
    (derivedDeltaDivisionStructure E dP a)
    (powerRootPrismMonicCompletionTorsionEquiv W hW f hf).toRingHom

powerRootPrismMonicCompletionHom_generator W hW f hf
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hd : g dP = Q.generator) :
  let := pdCompletionCommRing L p (jL dP)
  ∀ F : H →+* B, F.comp (uL.comp jL) = g →
    F (powerRootPrismMonicCompletionPrism W hW f hf).generator = Q.generator
```

f=1 の場合の同じ H の零環性も A1-b で処理されているため、旧主張を正次数版へ弱めていない。
原典 BS Rem 7.15（著者版 p.62）の p ねじれなしへの帰着とは異なる実源の純性の経路を
該当 docstring と本節に明記した。raw の mod p 分母正則性や T の p 正則性など、
一般に偽となる中間主張を無条件化していない。
残る R1 の旧公開名・呼出しの移行と不要定理の削除、A1-f の向きなし比較、
A1-c2 との最終合流は未完了。並列担当のファイルは編集していない。

監査：既存の9宣言の `assert_no_sorry` と個別9本の `#check` は終了コード0。専用監査は `André monic root audit passed: 8126 declarations, standard axioms only.`。型確認ログは `/tmp/andre-e183-retry-check.log`。同じ元の H と標準射を保つことを確認した。


## A1-f：向きなし prism への一般化

2026-10-17。A1-f として新規 `Andre/Unoriented/Category.lean` と
`Andre/Unoriented/Initial.lean` を実装し、同ディレクトリの `Audit.lean` で専用監査した。
E1.75・E1.80〜E1.82 と「A1-f への受渡し」の既存公開名・型・標準入力作用は変更していない。
BS Thm 1.17(1) と Cor 8.12、および既存の `Andre/` ファイルには触れていない。

### 対象と射

名前空間は `SerrePositivity.BhattScholze.Andre`。共通設定は
`{p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]`、
`W : OrientedPrism p A`、`c : A ⧸ W.ideal →+* S`。
`BoundedPrismInputUnoriented W c : Type (u+1)` は以下のデータ・条件を持つ。

```lean
ring : CommRingCat.{u}
delta : DeltaStructure p ring
base : A →+* ring
base_delta : W.deltaStructure.IsDeltaHom delta base
ideal : Ideal ring
ideal_eq : ideal = Ideal.span {base W.generator}
regular : Function.Injective (fun x : ring => base W.generator * x)
complete_p : DerivedCompletion.IsModuleComplete ring (p : ring) (ModuleCat.of ring ring)
complete_d : DerivedCompletion.IsModuleComplete ring (base W.generator) (ModuleCat.of ring ring)
p_mem : (p : ring) ∈ ideal ⊔ ideal.map delta.frobeniusLift
base_ideal : W.ideal ≤ ideal.comap base
input : S →+* ring ⧸ ideal
input_base : input.comp c = Ideal.quotientMap ideal base base_ideal
bounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : ring ⧸ ideal,
  (p : ring ⧸ ideal)^n*x = 0 → (p : ring ⧸ ideal)^N*x = 0
```

イデアル J 自体を保持するが、独立した生成元はデータとして持たない。
J が基底の d の像で生成されることを `ideal_eq` で要求し、正則性はこの主イデアルの
Cartier 条件として与える。導来完備性は既存 `OrientedPrism` と同じ p・d の表示を使う。
BS Def 3.2（著者版 pp.28–29）、Lemma 3.5（p.29）、Prop 3.13（pp.33–35）を確認した。
Prop 3.13 の普遍性を引用として導入せず、既存の証明済み初期性を使う。
B2 の完全 prism と perfectoid の対応は既存の向き付き構造を使用しており、今回も
完全性を標的へ課さず、基底 W のみに要求する。

`BoundedPrismInputUnoriented.orient X : BoundedPrismInput W c` は、生成元を
`X.base W.generator` とする。`orient_generator` はこの等式、`orient_ideal` は
`(orient X).prism.ideal = X.ideal` を証明する。入力は `Ideal.quotEquivOfEq X.ideal_eq`
に沿って標準商へ移す。射は `orient X ⟶ orient Y`、すなわち δ・イデアル・基底・入力を
保つ環射であり、生成元の厳密保存を追加しない。この射に既存の恒等射・合成を使って圏を作る。

### 忘却・標準的な向き・圏同値

`hW : W.deltaStructure.IsPerfect` の下で、公開型は次のとおり。
以下の補助名は `BoundedPrismInputUnoriented` 名前空間内。

```lean
orientFunctor : BoundedPrismInputUnoriented W c ⥤ BoundedPrismInput W c
forget hW (X : BoundedPrismInput W c) : BoundedPrismInputUnoriented W c
orientationIso hW (X : BoundedPrismInput W c) : orient (forget hW X) ≅ X
forgetFunctor hW : BoundedPrismInput W c ⥤ BoundedPrismInputUnoriented W c
equivalence hW : BoundedPrismInput W c ≌ BoundedPrismInputUnoriented W c
```

`forget` は元の台環・δ・イデアル・基底環射・入力作用・有界性をそのまま保つ。
`W.isDistinguished_of_perfect hW` と既存の
`boundedPrismHom_generator_span`・`boundedPrismHom_generator_regular`・
`boundedPrismHom_generator_complete` を使い、J=(d)B と基底の像の正則性・完備性を得る。
これらは `existsUnique_boundedPrismHom_generator_unit` を再利用した証明であり、
標的の完全性や p 正則性を前提に残さない。
`orientationIso` の往復と同値の単位・余単位はすべて台環上の恒等環射。
`forgetFunctor_map_toRingHom` は忘却関手が台の環射を変更しないことを証明する。
各向きなし対象 X は、同値の余単位により `forget hW (orient X)` と同型である。

### 向きなし圏での初期性の公開型

一般の移送は次の型で公開した。

```lean
BoundedPrismInput.initial_unoriented
    (hW : W.deltaStructure.IsPerfect)
    (X : BoundedPrismInput W c) (hX : IsInitial X) :
  IsInitial (BoundedPrismInputUnoriented.forget hW X)
```

元の正次数モニック源についての最終公開型は、名前空間
`SerrePositivity.BhattScholze.Andre` 内で正確に次のとおり。

```lean
powerRootPrismMonicSourceInput_initial_unoriented
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  IsInitial (BoundedPrismInputUnoriented.forget hW
    (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg))
```

E1.80 の元の H と、完備してから f で割る `PowerRootMonicCompletedInput` の標準作用を保つ。
`hreg`・`hBound`・`hpR` を追加仮定として残さない。
同じ宇宙 u・固定完全基底 W 上で J=(d)B を満たす対象についての結果である。
基底を動かした一般 Cartier イデアルの局所化降下や、絶対 prismatic site 全体の定式化まで
完了したとは数えない。E1.82 の絶対入力の既存公開名も変更していない。

### 検証と採用ファイル

すべて `set -o pipefail` 付きで実行した。

- 対象ビルド：`lake build SerrePositivity.BhattScholze.Andre.Unoriented.Initial`、
  終了コード0（4393 jobs）。新規実装モジュールの警告なし。
- 専用監査：`lake env lean SerrePositivity/BhattScholze/Andre/Unoriented/Audit.lean`、
  終了コード0。公開13宣言の `assert_no_sorry`、同値と最終初期性の型の固定、
  実装2モジュールの生成宣言を含む80宣言の推移的公理検査を実施した。
  許可公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- 集約ビルド：`lake build SerrePositivity SerrePositivity.BhattScholze.Andre.Unoriented.Initial`、
  終了コード0（7214 jobs）。既存ファイル由来の警告は保持した。
- ログ：`/tmp/andre-unoriented-initial.log`、`/tmp/andre-unoriented-audit.log`、
  `/tmp/andre-unoriented-aggregate.log`。

作業中に同名の構造を定義する別チャットの `Unoriented/InputCategory.lean` が現れた。
ユーザーの明示回答により、本チャットの `Category.lean`・`Initial.lean`・`Audit.lean` を採用する。
別チャットのファイルは編集・削除・取り込みしていない。
合流時の import は `SerrePositivity.BhattScholze.Andre.Unoriented.Initial` とし、
同名の別実装 `InputCategory` と併用しない。ルート集約ファイルへの import 追加は担当側に残す。
本節は既存の他担当節を変更せず末尾に追記した。保存対象は新規3ファイルと本節だけとし、
`git commit --only` で他担当の差分を巻き込まず保存する。

## A1-f：向きなし prism への一般化（集約と追加公開）

2026-10-17。本チャットの重複実装 `Unoriented/InputCategory.lean`・`Comparison.lean` は
取り下げ、採用済みコミット `6358b55c` の `Category.lean`・`Initial.lean`・`Audit.lean` を
そのまま参照する。既存ファイル・他担当節・R1 の移行には変更を加えていない。
新規 `Unoriented/SourceInitiality.lean`、集約 `Andre/Unoriented.lean`、
専用監査 `scripts/audit_andre_unoriented.lean` とルートの import 1 行を追加した。

### 固定基底と原典の範囲

原典は BS Def 3.2（著者版 p.28）、Lemma 3.5（p.29）、Prop 3.13（pp.33–35）、
Rem 7.15（p.62）を参照した（https://people.mpim-bonn.mpg.de/scholze/prisms.pdf）。
固定基底 (A,I) からの prism 射では Lemma 3.5 により IB=J であるため、I=(d) なら
J=(base(d)) となる。実装はこの固定基底上の表示を `ideal_eq` に持つ。
向き付き対象の忘却で必要なイデアル等式・正則性・完備性は、引用を追加せず
既存の `boundedPrismHom_generator_span`・`boundedPrismHom_generator_regular`・
`boundedPrismHom_generator_complete` から供給する。

採用済み圏同値の正確な型は、同じ宇宙 u、
`{A S : Type u} [CommRing A] [CommRing S] {p : ℕ} [Fact p.Prime]` の下で

```lean
BoundedPrismInputUnoriented.equivalence
    (W := W) (c := c) (hW : W.deltaStructure.IsPerfect) :
  BoundedPrismInput W c ≌ BoundedPrismInputUnoriented W c
```

である。台環・δ・実イデアル・入力作用を保ち、比較同型は台環上で恒等。
基底を動かす一般 Cartier イデアルの局所化降下や、絶対 site 全体の構築は範囲外。
一般 Cartier イデアルだけを与えた型からこの表示への帰着を今回新たに形式化したとはしない。
主定理・引用件数、BS Thm 1.17(1) と Cor 8.12 には触れていない。

### 追加公開5宣言の正確な型

名前空間はすべて `SerrePositivity.BhattScholze.Andre`。
共通設定は `{A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]`、
`W : OrientedPrism p A`、`hW : W.deltaStructure.IsPerfect`、
`f : Polynomial A`、`hf : f.Monic`、`hdeg : 0 < f.natDegree`。
以下の記号は既存の実環・標準入力そのものを指す。

```lean
hp := Nat.Prime.pos (Fact.out : p.Prime)
P := PowerRootPolynomial A p hp
E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
dP := algebraMap A P W.generator
a := powerRootPrismMonicUnaryFamily (p := p) f
L := DeltaAdjoinDivision E dP a
jL := deltaAdjoinDivisionMap E dP a
H := PDCompletionH0 L p (jL dP)
R := A ⧸ W.ideal
fR := f.map (Ideal.Quotient.mk W.ideal)
PR := PowerRootPolynomial R p hp
CR := AdicCompletion (Ideal.span {(p : PR)}) PR
zR := powerRootPolynomialBaseMap R p hp fR
SI := PowerRootMonicCompletedInput p hp fR
lS := (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})).comp (algebraMap PR CR)
cS := lS.comp (algebraMap R PR)
X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
```

公開型は次のとおり。

```lean
powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg :
  BoundedPrismInputUnoriented W cS

powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented W hW f hf hdeg :
  IsInitial (powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg)

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented W hW f hf hdeg
    (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) :
  let := pdCompletionCommRing L p (jL dP)
  H ≃+* Z.ring

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff_unoriented
    W hW f hf hdeg (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) (a₀ : A) :
  let := pdCompletionCommRing L p (jL dP)
  powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented W hW f hf hdeg Z hZ
    (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base a₀

existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented
    W hW f hf hdeg (Q : BoundedPrismInputUnoriented W cS)
    (η : SI →+* Q.ring ⧸ Q.ideal) :
  ∃! G : OrientedPrism.Hom X.prism Q.orient.prism,
    G.quotientMap.comp X.input = (Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η
```

最初の二つは採用済みの忘却対象・初期性への公開別名。
環同型は向きなし圏の初期対象の一意な同型から得て、その基底保存性から係数公式を得る。
最後の定理は E1.82 を標的の標準 orientation に適用する。
射の型に現れる `Q.orient` は基底生成元像によるもので、独立した向きの選択は不要。
η に既存の Q.base との可換性を仮定せず、基底保存条件も結論に追加しない。
標的 Q 自体は固定基底上の向きなし入力圏の対象に限る。

源の hreg・hBound・hpR は追加していない。hdeg は元の公開型を維持したもので、
零次数まで一般化したとはしない。比較先の hZ は初期対象同士の比較のための条件であり、
源の初期性の証明に残る条件ではない。

### 本チャットの検証

すべて `set -o pipefail` 付きで実行し、終了コード0を確認した。

- 集約対象：`lake build SerrePositivity.BhattScholze.Andre.Unoriented`、4412 jobs。
- 専用監査：`lake env lean scripts/audit_andre_unoriented.lean`。
  公開18宣言の `assert_no_sorry`、追加5宣言の `#check`、採用済み2モジュールと
  追加モジュールの生成宣言を含む135宣言の推移的公理検査に成功。
  許可公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- 全体：`lake build`、7216 jobs。新規実装モジュールの警告なし。
- ログ：`/tmp/andre-unoriented-final-build.log`、
  `/tmp/andre-unoriented-final-audit.log`、`/tmp/andre-unoriented-repository-build.log`。

保存は新規3ファイル、本節、ルートの import 1 行だけを `git commit --only` で行う。
ルートの他担当の import 差分はコミットに含めず、作業木に保持する。

### E1.84／R1 完全忠実平坦性の無条件版への移行（2026-10-17）

本節は A1-a／R1 の追記。元の Hodge–Tate 商の完全忠実平坦性の呼出しを
A1-b の `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional` へ移した。
新しい引用・sorry・axiom は追加していない。BS Rem 7.15（著者版 p.62）と異なる
実源の純性による経路を、変更したファイルの docstring に明記した。

まず `PowerRootPrismMonicHodgeTateRoot.lean` の import を
`HodgeTateCompletelyFaithfullyFlat` から必要な `HodgeTateBase` に狭めた。
根の2公開宣言の主張・証明は不変。この変更により、A1-b の標準入力の普遍性を使う証明と
旧完全忠実平坦性ファイルの間の循環を除いた。予定した import グラフに循環がないことを確認した。

不要になった次の旧3定理は、全コード・監査の呼出しを置換した後に削除した。
namespace は `SerrePositivity.BhattScholze.Andre`。

- `powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat`
- `powerRootPrismMonicHodgeTate_prime_completelyFlat`
- `powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat`

`PowerRootPrismMonicHodgeTateCompletelyFaithfullyFlat.lean` は既存 import 用の移行ファイルとし、
無条件版を公開する。`HodgeTateCompletelyFlat` の `regular_of_span_power_eq` と
`powerRootPrismMonicHodgeTate_varpi_regular` は A1-c2 の Candidate が使うため保持した。
これらの条件付き正則性を偽の無条件主張へ置換したわけではない。

合わせて、以下の9公開宣言から hpR を除いた。共通引数は
{A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、W:OrientedPrism p A、
hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic、hdeg:0<f.natDegree。
H と dH は E1.80 の元の構成で、必要な型には標準の pdCompletionCommRing を先頭の let で供給する。
I=Ideal.span {(p:A),W.generator}、Q=A/I、q=Ideal.Quotient.mk I、
c=powerRootPrismMonicCompletionBaseMap W hW f、M₀=baseChangeScalarModule c と置く。
Y₀ は `(boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M₀)` の台の導来対象。

```lean
powerRootPrismMonicCompletion_pair_completelyFlat W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  IsCompletelyFlat I H

powerRootPrismMonicCompletion_pair_scalarExtensionTorVanishing W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicCompletionAlgebra W hW f
  scalarExtensionTorVanishing q M₀

powerRootPrismMonicCompletion_pair_reduction_homology_isZero W hW f hf hdeg
    (i : ℤ) (hi : i ≠ 0) :
  let := pdCompletionCommRing L p (jL dP)
  IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj Y₀)

powerRootPrismMonicCompletion_pair_scalarExtension_faithfullyFlat W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M₀)

powerRootPrismMonicCompletion_pair_reductionH0_faithfullyFlat W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y₀)
```

残る4宣言は元の H の δ 完全化後の同じ環に関するもの。
DH=deltaPDCompletionStructure (deltaAdjoinDivisionStructure E dP a) (jL dP)、
Cp=DeltaPerfection DH、κ=deltaAlgebraPerfectionCoefficient DH c、
x=deltaPerfectionOf DH 0 dH（定義的に κ W.generator）、
Hp=PDCompletionH0 Cp p x、t=(pdCompletionUnit Cp p x).comp κ、
M∞=baseChangeScalarModule t、T∞=Hp/Ideal.span {pdCompletionUnit Cp p x x} と置く。
Y∞ は `(boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M∞)` の台の導来対象。
各型には H と Hp の標準環構造の let を先頭に置く。

```lean
powerRootPrismMonicCompletedPerfection_pair_homology_isZero W hW f hf hdeg
    (i : ℤ) (hi : i ≠ 0) :
  IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj Y∞)

powerRootPrismMonicCompletedPerfection_pairH0_faithfullyFlat W hW f hf hdeg :
  Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y∞)

powerRootPrismMonicCompletedPerfection_pair_completelyFaithfullyFlat W hW f hf hdeg :
  IsCompletelyFaithfullyFlat I (ModuleCat.carrier M∞)

powerRootPrismMonicCompletedPerfectionBaseMap_completelyFaithfullyFlat W hW f hf hdeg :
  let := (powerRootPrismMonicCompletedPerfectionBaseMap W hW f).toAlgebra
  IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ W.ideal)}) T∞
```

既存のモニック性・正次数・係数作用・環は保持し、hpR だけを除いた。
忠実性を要求するため零次数には拡張しない。A1-f と A1-c2 の既存ファイルは編集していない。
残る R1 の PD 包・raw 中間定理の呼出し移行と不要定理の整理、A1-f・A1-c2 の最終合流は未完了。

検証：ps で他レーンの lake build がないことを確認して対象ビルド（4486 jobs）を実行し終了コード0。文書修正後の対象・集約ビルド（4611 jobs）も終了コード0。import 整理で従来の一般補題3本が集約から外れていたことを監査が検出したため、集約へ `CompletelyFaithfullyFlatPrincipalPower` の明示 import を追加して従来の公開範囲を維持した。修正後の集約ビルド（4613 jobs）は `set -o pipefail` 付きで終了コード0。9更新宣言と置換先1宣言の10本の `#check` は終了コード0。専用監査は `André monic root audit passed: 8182 declarations, standard axioms only.`。削除した旧宣言の assert を除くとともに、置換先 `Unconditional.PowerRootHodgeTateReduction` 全宣言を監査範囲へ加えた。一般補題3本の assert とモジュール監査は維持した。

A1-f の保存済み成果 `6358b55c` の到着を確認した。既存定義は変更せず、R1 の保存後に公開型と範囲を読み、A1-c2 の成果と合わせた最終合流に用いる。

### E1.85／R1 Frobenius PD 包の旧8宣言を無条件版へ移行（2026-10-17）

本節は A1-a／R1 の追記。`PowerRootPrismMonicFrobeniusTensorPD.lean` と
`PowerRootPrismMonicFullFrobeniusPD.lean` の不要な hpR 付き公開宣言を各4本削除した。
同じ名前の `_of_unconditional` 版を `MonicRootedExtension` から明示的に公開する。
全リポジトリの Lean ファイルと監査で旧名を検索し、これら2ファイルの内部と自分の監査以外に
呼出しがないことを確認した。A1-c2 が使う native PD 包の旧名は変更していない。
並列担当の `Unconditional/` と `VarpiComparison/` のファイルは編集していない。

削除した8名は次のとおり。namespace は `SerrePositivity.BhattScholze.Andre`。
右に同じ名前へ `_of_unconditional` を付けた公開宣言が正本である。

- `powerRootPrismMonicFrobeniusTensorDividedPowers`
- `powerRootPrismMonicFrobeniusTensorInputAlgEquiv_isDPMorphism`
- `powerRootPrismMonicFrobeniusTensorDividedPowers_input_apply`
- `existsUnique_powerRootPrismMonicFrobeniusTensorPDMorphism`
- `powerRootPrismMonicFullFrobeniusDividedPowers`
- `powerRootPrismMonicFullFrobeniusInputAlgEquiv_isDPMorphism`
- `powerRootPrismMonicFullFrobeniusDividedPowers_input_apply`
- `existsUnique_powerRootPrismMonicFullFrobeniusPDMorphism`

旧2ファイルの係数作用・比較同型・指定 PD イデアル・入力の所属は保持する。
置換先は既存の `Unconditional/FrobeniusTensorPD.lean` と `Unconditional/FullFrobeniusPD.lean`。
モニック性を保持し、hpR と正次数仮定を要求しない。零次数 f=1 も含めた主張の範囲を維持する。
新しい引用・sorry・axiom は追加していない。BS Rem 7.15(1)（著者版 p.62）とは異なる
半線形比較・通常テンソル・分冪構造の移送という証明経路を変更した docstring に明記した。

公開8宣言の正確な型を共通記号で記す。引数は独立宇宙 u,w、{A:Type u} [CommRing A]、
{p:ℕ} [Fact p.Prime]、W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、
f:Polynomial A、hf:f.Monic。H,T,R,ϖ は E1.80 の元の構成、
Rp=R/(p)、Rv=R/(ϖ)、Np=PowerRootPolynomial Rp p hp、bp=(A→R→Rp)、
zp=powerRootPolynomialBaseMap Rp p hp (f.map bp)、Dp=PrincipalDPPresentation Np zp、
φ=powerRootPrismMonicHodgeTateBaseMap W hW f、Mv=T/Ideal.map φ (Ideal.span {ϖ}) とする。

二つの実台環 K と指定 J、比較 e、分冪構造 hK は次の対応である。

| K | J | e | hK |
|---|---|---|---|
| Ft=Rp⊗[Rv]Mv | `powerRootPrismMonicFrobeniusTensorPDIdeal W hW f hf` | `powerRootPrismMonicFrobeniusTensorInputAlgEquiv W hW f hf` | `powerRootPrismMonicFrobeniusTensorDividedPowers_of_unconditional W hW f hf` |
| At=TensorBaseCopy A⊗[A]Mv | `powerRootPrismMonicFullFrobeniusPDIdeal W hW f hf` | `powerRootPrismMonicFullFrobeniusInputAlgEquiv W hW f hf` | `powerRootPrismMonicFullFrobeniusDividedPowers_of_unconditional W hW f hf` |

Rp の Rv 作用は既存の `perfectPrismVarpiFrobeniusQuotientEquiv W hW` の作用。
At の左 A 作用は既存の `αc=(frobeniusEquiv W.deltaStructure hW).trans
(tensorBaseCopyRingEquiv A).symm`、右作用は自然な `powerRootPrismMonicVarpiBaseMap`。
各型には元の H の標準環構造・これらの標準代数構造・対応する
`powerRootPrismMonicFrobeniusTensorInputAlgebra` または `FullFrobeniusInputAlgebra` の let を先頭に置く。
比較先の構造 hDp は `powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf`。
各行の4公開宣言は正確に次の結論を持つ。

```lean
hK : DividedPowers J

-- 対応する ...InputAlgEquiv_isDPMorphism_of_unconditional
hK.IsDPMorphism hDp e.toRingHom

-- 対応する ...DividedPowers_input_apply_of_unconditional (n : ℕ)
hK.dpow n (algebraMap Np K zp) = e.symm (principalDPGenerator zp n)

-- 対応する existsUnique_...PDMorphism_of_unconditional
{B : Type w} [CommRing B] [Algebra Np B] {I : Ideal B}
(Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
∃! F : K →ₐ[Np] B, hK.IsDPMorphism Ht F.toRingHom
```

普遍性の標的には p ねじれなし・完備性・正則性を追加しない。
元の H や係数・根変数の像を変えず、旧8宣言を無条件な同じ計算の公開名へ移した。
残る R1 の native PD と raw 中間定理の整理、A1-c2・A1-f の最終合流は未完了。

検証：他レーンの lake build がないことを ps で確認し、`set -o pipefail` 付きで対象4モジュールと集約をビルドした（4616 jobs、終了コード0）。公開置換先8宣言の `assert_no_sorry` と8本の `#check` は終了コード0。専用監査は `André monic root audit passed: 8370 declarations, standard axioms only.`。置換先2モジュールの全生成宣言も監査範囲に加え、保持した旧モジュールの残る全宣言も引き続き監査した。

### E1.86／R1 ϖ 還元・mod p の旧PD公開5宣言を置換（2026-10-17）

本節は A1-a／R1 の追記。呼出しのない旧公開5宣言を削除し、同名の
`_of_unconditional` 版を集約から公開する。新規
`PerfectPrismVarpiPDUniversalUnconditional.lean` で係数消滅条件付きの普遍性を証明した。
他の4宣言は既存の `Unconditional/MonicPDEnvelope.lean` を使う。
`Unconditional/`・`VarpiComparison/`・`Unoriented/` のファイルは編集していない。
A1-c2 が現在呼ぶ旧 native 分冪構造とその入力公式は保持した。

置換した公開名（namespace `SerrePositivity.BhattScholze.Andre`）は次の5本。

- `existsUnique_perfectPrismVarpiPDMorphism_of_unconditional`
- `existsUnique_perfectPrismVarpiNativePDMorphism_of_unconditional`
- `powerRootPrimeFrobeniusDividedPowers_of_unconditional`
- `powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional`
- `existsUnique_powerRootPrimeFrobeniusPDMorphism_of_unconditional`

正確な型を共通記号で記す。引数は独立宇宙 u,v、{A:Type u} [CommRing A]、
{p:ℕ} [Fact p.Prime]、W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、
f:Polynomial A、hf:f.Monic。全5本に hpR・正次数仮定はない。
N0=PowerRootPolynomial (A/(p)) p hp、z0=powerRootCoefficientPDInput p f、
D0=PowerRootCoefficientPDEnvelope p f、a0 は perfectPrismVarpiLift W hW の A/(p) への像、
K0=Ideal.span {algebraMap (A/(p)) D0 a0}。
Rv=(A/W.ideal)/(ϖ)、Rp=(A/W.ideal)/(p)、Nv=PowerRootPolynomial Rv p hp、
Np=PowerRootPolynomial Rp p hp。zv,zp はそれぞれ f の自然な係数像の零段入力、
Dv=PrincipalDPPresentation Nv zv、Dp=PrincipalDPPresentation Np zp。
h0=`perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf`、
hv=`perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf`、
hpD=`powerRootPrimeFrobeniusDividedPowers_of_unconditional W hW f hf` とする。

```lean
-- existsUnique_perfectPrismVarpiPDMorphism_of_unconditional
{B : Type v} [CommRing B] [Algebra N0 B] {I : Ideal B}
(Ht : DividedPowers I) (hzB : algebraMap N0 B z0 ∈ I)
(haB : algebraMap N0 B (algebraMap (A/(p)) N0 a0) = 0) :
∃! F : (D0 ⧸ K0) →ₐ[N0] B, h0.IsDPMorphism Ht F.toRingHom

-- existsUnique_perfectPrismVarpiNativePDMorphism_of_unconditional
{B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
(Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
∃! F : Dv →ₐ[Nv] B, hv.IsDPMorphism Ht F.toRingHom

-- powerRootPrimeFrobeniusDividedPowers_of_unconditional
DividedPowers (principalDPPositiveIdeal zp)

-- powerRootPrimeFrobeniusDividedPowers_base_apply_of_unconditional (n : ℕ)
hpD.dpow n (algebraMap Np Dp zp) = principalDPGenerator zp n

-- existsUnique_powerRootPrimeFrobeniusPDMorphism_of_unconditional
{B : Type v} [CommRing B] [Algebra Np B] {I : Ideal B}
(Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
∃! F : Dp →ₐ[Np] B, hpD.IsDPMorphism Ht F.toRingHom
```

標的のねじれなし・完備性を追加せず、旧型の係数作用・入力と最初の係数消滅条件を保った。
BS Rem 7.15(1)（著者版 p.62）とは異なる射影的係数商・分冪構造移送を使う経路を
新規ファイルの docstring と本節に記録する。新しい sorry・axiom・引用はない。

検証：ps で他レーンの lake build がないことを確認して対象5モジュールと集約を
`set -o pipefail` 付きでビルドし、4618 jobs、終了コード0。
5本の型確認は終了コード0。専用監査は終了コード0、
`André monic root audit passed: 8425 declarations, standard axioms only.`。
5公開名の assert_no_sorry と、置換先3モジュールの全生成宣言を含めた監査を行った。
残る R1 の raw 正則性・native 構造の整理と A1-c2・A1-f の最終合流は未完了。

### E1.87／R1 旧公開2公式から hpR を除去（2026-10-17）

本節は A1-a／R1 の追記。次の2公開名を保持し、hpR だけを除いた。
名前空間は `SerrePositivity.BhattScholze.Andre`。

- `perfectPrismVarpiNativePDEnvelope_truncated_dpow`
- `powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete`

前者を新規 `PerfectPrismVarpiNativePDFormula.lean`、後者を新規
`PowerRootPrismMonicHodgeTateComplete.lean` に移した。
旧ファイル内の重複宣言は削除した。元の台環・標準射・切断同型・入力と添字は保持する。
後者は正次数を追加せず、零次数モニック f=1 も扱う。
前者の型に現れる分冪構造を既存の `_of_unconditional` 版へ変更した。
全 Lean ファイルの検索で、旧宣言を呼ぶ他ファイルがないことを確認した。
他レーンのファイルとルート集約は編集していない。

正確な型は以下。共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic。
Nv=PowerRootPolynomial ((A/W.ideal)/(ϖ)) p hp、zv は f の自然な係数像の零段入力、
Dv=PrincipalDPPresentation Nv zv。Raw、dL、H は従来の実 δ 除算包、標準分母像、
H=PDCompletionH0 Raw p dL をそのまま使う。

```lean
perfectPrismVarpiNativePDEnvelope_truncated_dpow W hW f hf (i : ℕ) :
  let := principalDPQuotientAlgebra hp
    (perfectPrismVarpiRootRing_prime_eq_zero W hW) zv
  perfectPrismVarpiNativePDEnvelope_truncatedEquiv W hW f
    ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow
      (p ^ (i + 1)) (algebraMap Nv Dv zv)) =
    Ideal.Quotient.mk _ (MvPolynomial.X i)

powerRootPrismMonic_pdCompletion_hodgeTate_isAdicComplete W hW f hf :
  let := pdCompletionCommRing Raw p dL
  let T := H ⧸ Ideal.span {pdCompletionUnit Raw p dL dL}
  IsAdicComplete (Ideal.span {(p : T)}) T
```

前者は射影的係数商による分冪降下、後者は正次数で有界ねじれと導来完備性の比較、
次数零で H の零環性を使う。BS Rem 7.15（著者版 p.62）の p ねじれなしへの帰着と
異なる経路であることを新規 docstring と本節に記す。
分母商自体の p 正則性を無条件に主張したものではない。

最初の検証では、自分が追加した NativePDFlat→Unconditional.MonicPDEnvelope の import が
既存の比較を経由して循環を作ることを検出した。分冪公式を新規ファイルへ移して
既存の依存順序を保つ形に修正した。依存先の破損や並行ビルド競合ではない。

修正中に検出した宣言の `include hf` 不足と集約 import の位置も修正した。
検証：各ビルド前に ps で他レーンの lake build がないことを確認した。
修正後の対象5モジュールと集約のビルドは `set -o pipefail` 付きで4620 jobs、終了コード0。
末尾整形後の集約ビルドも4620 jobs、終了コード0。
公開2本の #check と専用監査はそれぞれ終了コード0。
`assert_no_sorry` と新規2モジュールの全生成宣言を含む監査は
`André monic root audit passed: 8468 declarations, standard axioms only.`。

R1 の残り：A1-c2 が使う旧係数還元・native 分冪構造は、その呼出しが残るため保持している。
Raw 全体の p 正則性には別担当の無条件版がまだ到着していない。
mod p の分母正則性・分母商の p 正則性は hpR を一般には除けない主張なので、
単純に無条件版へ差し替えない。根環の δ 構造に使う係数環自身の p 正則性と、
標数 p を示す等式に付いた局所変数名 hpR は、prism 商の余分な仮定とは区別する。
A1-f の集約合流と A1-c2 を含む最終合流は未完了。

### E1.88／A1-f 保存済み成果を本レーンの集約・監査へ合流（2026-10-17）

本節は A1-a の追記。A1-f の保存済み `6358b55c`・`f6cf93b1` を読み、
`Andre.Unoriented` を自分の集約 `MonicRootedExtension` から公開した。
A1-f のファイルは編集していない。ルートの他レーンの import も編集・stage していない。
自分の専用監査に公開18宣言の assert_no_sorry と、
`Unoriented.Category`・`Unoriented.Initial`・`Unoriented.SourceInitiality` の全生成宣言を加えた。

主張の範囲：固定完全基底 W 上で J=(base(d)) を満たす向きなし有界入力対象の圏。
独立な生成元は持たず、基底の d の像による標準 orientation と既存の入力圏との同値を使う。
一般の Cartier イデアルの降下や全基底を動かす絶対サイトを実装したという主張には拡張しない。
BS Def 3.2（著者版 pp.28–29）と Rem 7.15（p.62）に対応する固定基底の結果であり、
Prop 3.13 を新たに引用しない。原典とは異なる圏同値・元の源の初期性の移送を使う。

共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、
hf:f.Monic、hdeg:0<f.natDegree。
R=A/W.ideal、SI=PowerRootMonicCompletedInput p hp (f.map (Ideal.Quotient.mk W.ideal))、
cS:R→+*SI は標準係数射、H は元の PDCompletionH0。
X=powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg、
Xu=powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg とする。
合流した主要公開名の正確な型は次のとおり。

```lean
-- BoundedPrismInputUnoriented.equivalence (任意の c : R →+* S)
BoundedPrismInputUnoriented W c ≌ BoundedPrismInput W c

powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg :
  BoundedPrismInputUnoriented W cS

powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented W hW f hf hdeg :
  IsInitial Xu

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented W hW f hf hdeg
  (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) :
  let := pdCompletionCommRing Raw p dL
  H ≃+* Z.ring

powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff_unoriented
  W hW f hf hdeg (Z : BoundedPrismInputUnoriented W cS) (hZ : IsInitial Z) (a₀ : A) :
  let := pdCompletionCommRing Raw p dL
  powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented
    W hW f hf hdeg Z hZ (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base a₀

existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented W hW f hf hdeg
  (Q : BoundedPrismInputUnoriented W cS) (η : SI →+* Q.ring ⧸ Q.ideal) :
  ∃! G : OrientedPrism.Hom X.prism Q.orient.prism,
    G.quotientMap.comp X.input = (Ideal.quotEquivOfEq Q.ideal_eq).toRingHom.comp η
```

最後の型は η と Q.base との可換性を追加仮定にしない。
全主張で元の H・入力環 SI・標準入力作用を保持し、hpR・hreg・hBound を追加しない。
A1-f の既存の正次数仮定は保持する。残る R1 と A1-c2 を含む最終合流は未完了。

検証：ps で他レーンの lake build がないことを確認して、向きなし集約・同 Audit と
本レーン集約を `set -o pipefail` 付きでビルドし、4626 jobs、終了コード0。
主要5公開名の #check は終了コード0。
A1-f 専用監査は `André unoriented audit passed: 135 declarations, standard axioms only.`、
本レーン監査は `André monic root audit passed: 8603 declarations, standard axioms only.`、
ともに終了コード0。後者では assert の挿入でずれた局所 `open Lean in` と
`maxHeartbeats` の適用位置を run_cmd の直前へ戻してから再実行した。
新しい sorry・axiom・引用は追加していない。

### E1.89／R1 元の raw p 正則性と通常 p 完備化の公開名を移行（2026-10-17）

本節は A1-a／R1 の追記。A1-b の保存済み `cd7ca7ed`・`c21e67c4` を受領し、
旧 hpR 付き2公開名を削除した。namespace は `SerrePositivity.BhattScholze.Andre`。

- `powerRootPrismMonicRaw_p_mul_injective` → `powerRootPrismMonicRaw_p_mul_injective_of_unconditional`
- `powerRootPrismMonicRaw_pAdic_regular_pair` → `powerRootPrismMonicRaw_pAdic_regular_pair_of_unconditional`

prism 商の p 正則性を要求する元の分母商の定理
`powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular` の内部の raw p 正則性呼出しも
無条件版に移した。この分母商の型から hpR を除いたものではない。
元の Raw と標準係数射を保持し、正次数もねじれ除去商も追加しない。
f=1 は raw 環の安定局所化への単射性と分母の単元性で処理する。
BS Rem 7.15（著者版 p.62）とは異なる実源の純性・導来完備化比較による経路である。
変更した docstring と本節でこの差を明記する。

共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic。
hp=Nat.Prime.pos (Fact.out:p.Prime)、P=PowerRootPolynomial A p hp、
E=powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure、
dP=algebraMap A P W.generator、a=powerRootPrismMonicUnaryFamily f、
Raw=DeltaAdjoinDivision E dP a、jL=deltaAdjoinDivisionMap E dP a とする。
正確な公開型は次のとおり。

```lean
powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf :
  Function.Injective (fun r : Raw => (p : Raw) * r)

powerRootPrismMonicRaw_pAdic_regular_pair_of_unconditional W hW f hf :
  let CP := AdicCompletion (Ideal.span {(p : Raw)}) Raw
  IsSMulRegular CP (p : CP) ∧
    IsSMulRegular CP (algebraMap Raw CP (jL dP))
```

全 Lean コードと監査を検索し、削除した2名の呼出しが残らないことを確認した。
`RawRegular` は一元自由 δ 環の型と有限段の条件付き正則対を保持する。
`RawPairRegular` は mod p 分母の条件付き正則性と実二座標完備化の無条件正則性を保持する。
無条件版からこれらへの import 経路を調べ、循環を追加しないことを確認した。
`Unconditional/`・`VarpiComparison/`・`Unoriented/` は編集していない。
R1 の残りは A1-c が使う旧 native 分冪構造・係数還元構造の整理と、係数計算の最終合流。

検証：ps で他レーンの lake build がないことを確認してから対象5モジュールと集約を
`set -o pipefail` 付きでビルドし、4660 jobs、終了コード0。
置換先2本と保持した分母商の条件付き公開名の #check は終了コード0。
専用監査は終了コード0、`André monic root audit passed: 8653 declarations, standard axioms only.`。
置換先2名の assert_no_sorry と、新規に import した2モジュールの全生成宣言も監査した。
新しい sorry・axiom・引用を追加していない。

## A1-c2

2026-10-17。担当範囲は `Andre/VarpiComparison/` の hpR 除去と本節。
BS Rem 7.15（著者版 p.62）を出典とし、旧名は A1-e のため保持した。
既存の VarpiComparison ファイル、Unconditional 側、集約 import は編集していない。

Unconditional の `PowerRootHodgeTateReduction`・`PrimeReductionPurity`・
`MonicPDEnvelope`・`VarpiPDReduction` から import 閉包を先に検査した。
外部モジュールの葉を含む 1000 モジュールに循環はなく、VarpiComparison への逆参照もない。
A1-a の既存の共有係数定義・作用をそのまま利用し、移動は不要だった。

公開名は全て `SerrePositivity.BhattScholze.Andre.VarpiComparison` 名前空間。
`W : OrientedPrism p A`、`hW : W.deltaStructure.IsPerfect`、`f : Polynomial A`、
`[CommRing A] [Fact p.Prime]` を共通引数とする。以下では
`R=A/W.ideal`、`v=perfectPrismVarpi W hW`、`Rv=R/(v)`、`R₀=A/(p)`、
`D=PowerRootCoefficientPDEnvelope p f`、`Nv=PowerRootPolynomial Rv p hp`、
`zv` は f の自然な Rv 係数像の無限根入力、`Dv=PrincipalDPPresentation Nv zv`、
`e=perfectPrismPDTensorVarpiEquiv W hW f` と略記する。

`UnconditionalPD.lean` の三宣言：

- `perfectPrismPDTensorVarpiDividedPowers_of_unconditional W hW f hf`：
  `DividedPowers ((principalDPPositiveIdeal zv).map e.symm.toRingHom)`。
- `perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional W hW f hf i`：
  上の構造の `dpow i (1 ⊗ algebraMap _ D (powerRootCoefficientPDInput p f))` が
  `1 ⊗ principalDPGenerator (powerRootCoefficientPDInput p f) i` に等しい。
- `perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional W hW f hf`：
  元の `powerRootCoefficientDividedPowers p W hW f hf` から上の構造への
  `Algebra.TensorProduct.includeRight.toRingHom` は `IsDPMorphism`。

いずれも `hf : f.Monic` だけを追加し、hpR も正次数も要求しない。
通常テンソルの係数作用は既存の `varpiCoefficientAlgebra W hW` に一致する。
分冪射は生成元だけでなく全ての元で標準射と照合した。

`UnconditionalCandidate.lean` の二宣言。T は元の Hodge–Tate 候補、
`Tv=T/(v)`、`f'=perfectPrismInverseFrobeniusPolynomial W hW f`、
`zv'` は f' の Rv 係数像の入力、`Qv=Nv/(zv'^p)` と略記する。
環・代数作用の let は旧定理と同じ：

```lean
hodgeTate_completelyFaithfullyFlat_iff_of_unconditional W hW f
  (hf : f.Monic) :
  IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔
    Module.FaithfullyFlat Rv Tv

hodgeTate_coefficient_comparison_of_unconditional W hW f
  (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔
    Module.FaithfullyFlat Rv Tv) ∧
  Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
  IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
  Nonempty (Rv ⊗[R₀] PowerRootCoefficientPDEnvelope p f' ≃+* Tv)
```

同値の正次数分岐では A1-b の実際の導来 p 還元による完全忠実平坦性を使う。
次数零分岐では `powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero` により
H とその商 T が零環となるため通常平坦性を使い、ϖ 剰余の忠実性を仮定から戻す。
同値に新たな hdeg は追加していない。一般加群 M の通常商による逆向き判定には
承認どおり M 上の ϖ 正則性が必要で、既存 `Flatness.lean` の hMv を保持する。
H の p 正則性から、その分母商 T の p・ϖ 正則性を無条件に推論していない。

専用監査は `UnconditionalAudit.lean`。五公開宣言の `assert_no_sorry` と
`#print axioms`、二モジュールの生成宣言込み公理検査、型・opaque 値を辿る依存グラフ検査を行う。
旧 hpR 付きの三つのテンソル分冪宣言・二つの候補比較宣言、旧 native 分冪構造・
係数還元分冪構造と公式・分冪射、旧候補の ϖ 正則性への依存を明示的に拒否する。
二つの候補比較の結論が旧名と同じ型であることも Lean の例で検査する。

検証：`lake build SerrePositivity.BhattScholze.Andre.VarpiComparison.UnconditionalCandidate`
は 4425 jobs、専用 `UnconditionalAudit` は 4428 jobs で成功。
五公開宣言は全て `propext`・`Classical.choice`・`Quot.sound` のみ。
二モジュールの生成宣言込み 18 宣言も標準三公理のみ。
公開五宣言を起点とする型と値の 6769 依存宣言に、禁止した旧 hpR 宣言はなかった。
構文の autoParam 値は論理的証明項と区別し、import 済み定理の公理情報には
Lean 標準の `collectAxioms` を用いる。二つの旧比較との結論の型検査も成功した。
新しい sorry・axiom・引用は追加していない。
全体ビルドはこの担当の検証には実行していない。

### E1.90／A1-c2・A1-f と元の初期源の最終比較を合流（2026-10-17）

本節は A1-a の追記。A1-c2 の `733631d5`・`94bbd0fb`・`1f50122d` と、
A1-f の保存済み成果を、自分の新規 `PowerRootPrismMonicCoefficientComparison.lean` で合流する。
`VarpiComparison/`・`Unconditional/`・`Unoriented/` のファイルは編集していない。
主定理の引用入力、ルート集約、BS Thm 1.17(1) と Cor 8.12 は変更していない。

作業中に用意した独立の係数テンソル構造・係数比較は、A1-c2 の成果の到着により重複した。
未コミットの重複実装は残さず、受領した五つの `_of_unconditional` 公開名を直接使う。
本工程の新規公開宣言は一つだけである。

`SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSource_initial_and_coefficient_comparison`。
共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、
hf:f.Monic、hdeg:0<f.natDegree。
Raw,L,jL,H,uL,dP,T,R,v,Rv,φ は元の構成。Tv=T/Ideal.map φ (Ideal.span {v})、
f'=perfectPrismInverseFrobeniusPolynomial W hW f、Nv=PowerRootPolynomial Rv p hp、
zv は f' の Rv 係数像の零段入力、Qv=Nv/(zv^p)、R₀=A/(p)、
Xu=powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg。
正確な型は次のとおり。標準環構造と全係数作用を明示している。

```lean
powerRootPrismMonicSource_initial_and_coefficient_comparison W hW f hf hdeg :
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := VarpiComparison.hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := VarpiComparison.varpiCoefficientAlgebra W hW
  Nonempty (CategoryTheory.Limits.IsInitial Xu) ∧
    (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔
      Module.FaithfullyFlat Rv Tv) ∧
    Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
    Nonempty (Rv ⊗[R₀] PowerRootCoefficientPDEnvelope p f' ≃+* Tv)
```

元の H の向きなし初期性の実証人と A1-c2 の無条件係数比較をそのまま合流した証明である。
hpR・hreg・hBound を追加仮定に残さない。f' の逆 Frobenius 係数変更は省略しない。
初期性は固定完全基底上の J=(d)B の入力圏についての主張であり、
一般 Cartier イデアルの降下へ範囲を広げない。BS Rem 7.15(1)（著者版 p.62）とは
異なる実源の純性・圏同値を使う証明経路を docstring と本節に明記する。

受領した次の五公開名も集約と監査へ加えた。namespace は
`SerrePositivity.BhattScholze.Andre.VarpiComparison`。

- `perfectPrismPDTensorVarpiDividedPowers_of_unconditional`
- `perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional`
- `perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional`
- `hodgeTate_completelyFaithfullyFlat_iff_of_unconditional`
- `hodgeTate_coefficient_comparison_of_unconditional`

前三本は hf のみ、同値も hf のみ、最後の比較のみ hf と hdeg を要求する。
正確な分冪イデアル・標準 includeRight・型は直前の A1-c2 節のとおりであり、変更していない。
同値の零次数分岐を保ち、余分な正次数を付けた弱い同値へ差し替えていない。
さらに `Unconditional.RawInitialRegular` の全生成宣言と、モニック初期関係・深さ零有限商の
無条件な正則性の二公開名も集約から明示公開し、assert_no_sorry を追加した。
それぞれの前提は元の hf であり、初期関係には hW も不要、変数族の宇宙 v は独立である。

監査は全対象モジュールの全生成宣言の標準三公理検査に加え、最終合流・向きなし初期性・
向きなし絶対入力普遍性・A1-c2 五公開名を根とする型と opaque 値の依存を辿る。
旧 hpR 付き11宣言への逆依存を拒否する。Syntax の既定タクティクは証明依存と区別し、
A1-c2 の検証済みの探索方法を自分の監査スクリプト内で用いる。

R1 の残り：旧 native 構造二名と係数還元構造三名は、A1-c の旧 PDBaseChange・
PDCompatibility と UnconditionalAudit の旧名検査が参照しているため保持している。
本工程の新規最終定理と A1-c2 五公開名はこれらに依存しない。
「他チャットのファイルを編集しない」の範囲を守っており、旧呼出し側をまだ変更していない。
原典の p ねじれなしへの帰着に対応する八つの強い正則性主張も、無条件化せず保持する。
この旧 API の整理を含む R1 全体の完了とは数えない。

検証：各 lake build 前に ps で他レーンの lake build がないことを確認した。
受領成果を直接使う最終の対象3モジュールと集約は `set -o pipefail` 付きで
4671 jobs、終了コード0。新規1名・受領5名・初期関係2名の8本の #check は終了コード0。
A1-c2 の専用 UnconditionalAudit は18生成宣言が標準三公理のみ、
6769 の型・値依存に旧 hpR 宣言への依存がないことを再確認した。
本レーン専用監査は終了コード0、
`André monic root audit passed: 9087 declarations, standard axioms only.`、
`André merged dependency audit passed: 49806 declarations, no legacy hpR dependencies.`。
対象モジュールの全生成宣言と公開名の assert_no_sorry を検査した。
新しい sorry・axiom・引用は追加していない。

### E1.91／R1 承認された呼出し移行と旧分冪5宣言の削除（2026-10-17）

本節は A1-a／R1 の追記。利用者から、A1-c2 の既存3ファイル
`VarpiComparison/PDBaseChange.lean`・`PDCompatibility.lean`・`UnconditionalAudit.lean`
に限って変更する明示承認を受けた。用意した差分の範囲で呼出しを移行した。
それ以外の他レーンのファイル・節は編集していない。

旧 native 分冪構造2宣言と係数還元構造3宣言を削除した。namespace は
`SerrePositivity.BhattScholze.Andre`。いずれも右の同名 `_of_unconditional` 版を正本とする。

- `perfectPrismVarpiNativeDividedPowers`
- `perfectPrismVarpiNativeDividedPowers_base_apply`
- `perfectPrismVarpiPowerRootDividedPowers`
- `perfectPrismVarpiPowerRootDividedPowers_base_apply`
- `perfectPrismVarpiPowerRootDividedPowers_isDPMorphism`

`PerfectPrismVarpiNativePDEnvelope` は元の比較と一般普遍性の import を保つ入口とした。
後続の無条件版をこの入口から import すると循環になるため、無条件版は集約から公開する。
空になった同モジュールを全生成宣言の監査配列から外し、正本のモジュール監査は保持した。
`PerfectPrismVarpiRegular` の二つの本質的な正則性補題と一般の順序交換補題は保持した。

共通引数は {A:Type u} [CommRing A]、{p:ℕ} [Fact p.Prime]、
W:OrientedPrism p A、hW:W.deltaStructure.IsPerfect、f:Polynomial A、hf:f.Monic。
R₀=A/(p)、N=PowerRootPolynomial R₀ p hp、z=powerRootCoefficientPDInput p f、
D=PowerRootCoefficientPDEnvelope p f、J=principalDPPositiveIdeal z、
x は perfectPrismVarpiLift W hW の R₀ への像、K=Ideal.span {algebraMap R₀ D x}、
q:D→+*D/K は標準商射。
Rv=(A/W.ideal)/(ϖ)、Nv=PowerRootPolynomial Rv p hp、zv は f の自然な Rv 係数像の零段入力、
Dv=PrincipalDPPresentation Nv zv とする。置換先5本の正確な型は次のとおり。

```lean
perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf :
  DividedPowers (principalDPPositiveIdeal zv)

perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional W hW f hf (n : ℕ) :
  (perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow n
    (algebraMap Nv Dv zv) = principalDPGenerator zv n

perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf :
  DividedPowers (J.map q)

perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional W hW f hf (n : ℕ) :
  (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf).dpow n
    (q (algebraMap N D z)) = q (principalDPGenerator z n)

perfectPrismVarpiPowerRootDividedPowers_isDPMorphism_of_unconditional W hW f hf :
  (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf) q
```

いずれも hpR・hdeg を要求しない。零次数 f=1 と零係数環も元の範囲のまま扱う。
BS Rem 7.15(1)（著者版 p.62）とは異なる射影的係数商・線形切断・構造移送の経路。
変更した docstring と本節にこの差を記録する。

承認された呼出し側の次の三公開名からも hpR を除いた。namespace は
`SerrePositivity.BhattScholze.Andre.VarpiComparison`。
`e=perfectPrismPDTensorVarpiEquiv W hW f`、
`Ht=perfectPrismPDTensorVarpiDividedPowers W hW f hf` とする。
全ての型の先頭に `let := varpiCoefficientAlgebra W hW` を置く。

```lean
perfectPrismPDTensorVarpiDividedPowers W hW f hf :
  DividedPowers ((principalDPPositiveIdeal zv).map e.symm.toRingHom)

perfectPrismPDTensorVarpiDividedPowers_generator W hW f hf (i : ℕ) :
  Ht.dpow i (1 ⊗ₜ[R₀] algebraMap N D z) = 1 ⊗ₜ[R₀] principalDPGenerator z i

perfectPrismPDTensorVarpi_isDPMorphism W hW f hf :
  (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism Ht
    (Algebra.TensorProduct.includeRight : D →ₐ[R₀] Rv ⊗[R₀] D).toRingHom
```

環・作用・生成元・全元での自然射の照合は保持した。
二つの監査で削除済み旧5名を実定数として参照せず、完全修飾した Name リテラルで禁止する。
従って旧名がない現在も検査でき、将来の再導入に対しても拒否条件を弱めない。
旧名を全リポジトリの Lean ファイルと監査で検索し、禁止 Name リテラル以外に
参照がないことを確認した。

検証：ps で他レーンの lake build がないことを確認して、変更対象・A1-c の両監査と集約を
`set -o pipefail` 付きでビルドした。4672 jobs、終了コード0。
置換先5名・hpR を除いた呼出し側3名・最終比較と根付き拡大・絶対入力普遍性の
計12本の #check は終了コード0。
A1-c の既存監査は100生成宣言が標準三公理のみ。
A1-c2 の監査は18生成宣言が標準三公理のみ、6769 の型・値依存に旧 hpR 宣言なし。
本レーン専用監査は終了コード0、
`André monic root audit passed: 9029 declarations, standard axioms only.`、
`André merged dependency audit passed: 49806 declarations, no legacy hpR dependencies.`。
新しい sorry・axiom・引用は追加していない。

最終完了監査：最新の利用者指示に従い、A1-e は起動・再開せず R1 を本担当が進めた。
受渡し節は A1-f 向けの保存すべき公開名だけである。
E1.82 の絶対入力普遍性、A1-f の固定完全基底上の圏同値・初期性、A1-c2 の無条件な
係数比較を、同じ H・標準係数作用のまま集約し、公開型・証明・監査で照合した。
E1.90 の新規最終比較の正確な型と hf・hdeg だけの前提はその節のとおり。

R1 の累積整理は、旧分冪18名・raw2名・完全平坦性3名の合計23宣言が
全 Lean コードからなくなったことを確認した。E1.83・84・87 の仮定除去も保持している。
一方、A1-b が分類した八つの強い正則性主張と、それから得る候補の条件付き ϖ 正則性は
数学的に別の主張なので保持する。prism 商が標数 p の場合まで無条件化しない。
係数環自身の p 正則性・標数条件を表す別種の hpR も保持する。
A1-c の旧 Candidate の二比較は、A1-c2 の型一致検査の基準として元の署名を保持する。
新しい公開根がこれらを経由しないことは上記の型・opaque 値の禁止依存監査で検証済み。
これらの条件付き比較を、一般の perfectoid 基底に対する完成定理として数えていない。

一段の任意族の公開出力は、利用者が承認した hdeg を含む次の型を保つ。

```lean
exists_monicRootedPerfectoidExtension
  (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
  (hR : IsIntegralPerfectoid R p) {σ : Type u}
  (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
  (hdeg : ∀ s, 0 < (f s).natDegree) :
  ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
    IsIntegralPerfectoid T p ∧
    (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
    ∀ s, (f s).eval₂ φ (ρ s) = 0
```

root の本レーン集約 import は1行で、今回 root 自体は変更していない。
単一入力・有限族・任意族と完備化の既存の構成、原典の順序の完備入力 SI、
元の H の固定基底上の初期性、Frobenius 係数変更を保つ pd 比較は全て公開入口から参照できる。
以上により、最新指示の R1 と A1-c2・A1-f の最終合流について必要な未完了作業はない。
一般 Cartier イデアルの降下、基底を動かすサイトの一般化は今回の固定基底の担当範囲に含めない。
全リポジトリの build や他レーンの引用入力の変更を実施したという主張ではない。
