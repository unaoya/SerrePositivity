# AR-W1 段 1 の報告

現在地は段 1 の調査完了。基準は main `eac7d1e57`、調査枝は `refactor/audit-review`。
現行 Lean 423 本を一行ずつ、Python の構造検査と回帰試験 61 本を別表に収めた。
`scripts/archive/` の Lean は 1 本。数だけを記録した。
ソースと監査 manifest を基準のまま使った。[Lean の調査表](../../../research/audit-review/stage1.csv)と[Python の構造検査](../../../research/audit-review/python.csv)。

## 実行と診断

root と監査の import 対象を bulk 鍵でビルドし、Lean の実行は一度に一本とした。
元のスクリプトを Lake の環境で実行し、経過時間と `/usr/bin/time -l` の最大 RSS を採った。
補助 CLI は引数を要するため、小さい実例を指定し、その実行結果もログに保存した。
分類はソースのコマンド・条件による。複数の種類を持つスクリプトは各行に含めた。
`type_examples` は既存宣言を明示した型へ当てる検査、`applied_examples` はその他の証明・適用例と `#guard` の件数。
`axiom_count` は許可公理を判定する対象の宣言集合の大きさ。明示コマンドや印字は別列。
集合は所有モジュールとカーネル名で照合し、同名の生成宣言は当該 import 環境が選ぶ所有元を使った。
失敗した行の宣言集合には、ソースの選択条件を現在の import に当てた範囲を載せた。
失敗の発生時点は基準コミットでの再現と、旧名の移動記録や以前の実行結果で確認できる手掛かりを示した。
精密化の索引が得られなかった名指しは、ソースと所有元から解決できたものを数えた。
印字とは別に、結果を判定する条件を数えた。

| 種類 | manifest 掲載 本数 / 行数 / 延べ時間 | 非掲載 本数 / 行数 / 延べ時間 |
| --- | --- | --- |
| 全体 | 108 本 / 175,902 行 / 1.44 時間 | 315 本 / 26,797 行 / 47.0 分 |
| 公理 | 76 本 / 114,771 行 / 1.05 時間 | 300 本 / 25,304 行 / 42.1 分 |
| sorry | 97 本 / 128,186 行 / 1.29 時間 | 286 本 / 23,819 行 / 42.9 分 |
| 存在・型 | 40 本 / 93,734 行 / 36.7 分 | 298 本 / 25,137 行 / 44.6 分 |
| 印字 | 76 本 / 133,648 行 / 50.9 分 | 1 本 / 57 行 / 0.2 分 |
| 使ってみる | 16 本 / 43,010 行 / 17.9 分 | 134 本 / 11,692 行 / 16.8 分 |
| 構造 | 23 本 / 57,394 行 / 26.5 分 | 72 本 / 5,866 行 / 10.9 分 |
| その他 | 0 本 / 0 行 / 0.0 分 | 4 本 / 708 行 / 0.8 分 |

| 最初の診断 | 掲載 | 非掲載 |
| --- | --- | --- |
| 合計 | 0 | 163 |
| 名前が見つからない | 0 | 110 |
| 型・証明の不一致 | 0 | 4 |
| 宇宙引数・暗黙変数 | 0 | 21 |
| 検査の条件違反 | 0 | 28 |

ファイル上限の試行は、スクリプト固有の失敗の集計から外した。
`Too many open files in system` は 2 本、延べ 2 回。
使用中・解放可能の vnode と共有鍵の保持状況を確認し、他の全体読み込みと重ならない枠で再試行した。
マシンの記録値は `kern.maxfiles = 491520`、`kern.maxvnodes = 263168`。

| スクリプト | 診断が出た回数 | 再試行後 | 最終所要時間 | 最終診断 |
| --- | --- | --- | --- | --- |
| `scripts/audit_axioms.lean` | 1 | 通る | 244.1 秒 |  |
| `scripts/refactor/audit_sorries.lean` | 1 | 通る | 177.4 秒 |  |

ファイル上限以外の環境診断も別に保存した。最終判定には再試行の結果を使った。

| スクリプト | 根拠 | 試行秒 |
| --- | --- | --- |
| scripts/audit_axioms.lean | artifact-lookup-while-present | 248.487 |

## 全体の検査二本が実際に見る範囲

母集団は Archive を除く本体 34,250 モジュールのカーネル宣言 360,168 件。
所有元を保持し、公開・private・生成宣言を含む。root の import 閉包は 29,863 モジュール、宣言 314,121 件。

- `scripts/audit_axioms.lean` は `SerrePositivity` を import する。公理を印字する本体宣言は 53 件、sorry の印字は 1 件。
  印字しない本体宣言は 360,115 件。許可公理の集合との照合は行わないので、許可公理の検査としては全 360,168 件が範囲外。
  明示の `assert_no_sorry` は本体 48 件で、360,120 件はその名指しの範囲外。
  さらに主定理から二つの旧 BS surjectivity 入口に届かないことを検査する。
- `scripts/refactor/audit_sorries.lean` は、既定では `main_statement` の型と本体から定数の辺をたどる。
  実行ログの訪問は外部を含め 102,468 定数。保存成果物で同じ辺を読み、本体所有元では 21,792 件に到達。
  全体では 338,376 件、root の import 閉包の内側でも 292,329 件が範囲外。
  直接の sorry の親が許可 3 件と一致すること、Kan–Quillen の旧入口が閉包にないことを検査する。
  宣言ごとの許可公理・型や、root の import 閉包全体を調べる検査とは条件が異なる。

## 領域の監査を消すと失われる検査

manifest の領域監査のうち 40 本が本定理の閉包と交差し、7 本では検査対象の名指しがすべて閉包に入る。
`audit_axioms.lean` の公理印字と名指しが交差する領域監査は 5 本。検査として許可公理を判定するものは、同ファイルに該当する条件がない。
厳格な sorry 非依存の名指しが明示一覧と交差する監査は 3 本、すべて含まれる監査は 0 本。
領域監査 76 本が許可公理の集合と比べる対象は、所有元付きの和集合で 261,830 宣言。
許可公理の集合、個々の宣言の sorry 非依存、型・適用例、構造条件を区別して比較した。
下表の「公理」は許可公理と照合する宣言の件数。「sorry 残」は全体の明示 `assert_no_sorry` からこぼれる厳格条件。
名前の集合と検査条件がともに含まれる候補は CSV の `other_axiom_supersets` と `other_sorry_supersets` に示す。

| scripts/ からのパス | 現状 | 公理 | sorry 残 | 型・適用例 | 構造 | 単独 import | 残る条件 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| audit/adams.lean | 通る | 2277 | 0 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 2277 宣言の推移的公理依存。sorryAx または証明本体の sorry |
| audit/bhatt_scholze.lean | 通る | 20909 | 0 | 0 | 0 | 1 | 所有モジュール／名前空間から選ぶ 20909 宣言の推移的公理依存。sorryAx または証明本体の sorry |
| audit/bs_power_root_envelope/InitialCoefficient.lean | 通る | 185 | 185 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 185 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 20 命令。型指定: rawResidue_faithfullyFlat |
| audit/bs_power_root_envelope/Unoriented.lean | 通る | 160 | 160 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 160 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 13 命令。型指定: BoundedPrismInputUnoriented.equivalence |
| audit/bs_power_root_envelope/VarpiComparison.lean | 通る | 104 | 104 | 0 | 2 | 0 | 所有モジュール／名前空間から選ぶ 104 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 29 命令 |
| audit/bs_power_root_envelope/VarpiComparisonUnconditional.lean | 通る | 104 | 104 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 104 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 5 命令。型指定: Subsingleton.elim |
| audit/clmst.lean | 通る | 271 | 0 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 271 宣言の推移的公理依存。sorryAx または証明本体の sorry |
| audit/dg.lean | 通る | 15656 | 0 | 0 | 0 | 304 | 所有モジュール／名前空間から選ぶ 15656 宣言の推移的公理依存。sorryAx または証明本体の sorry |
| audit/shared.lean | 通る | 17599 | 0 | 0 | 0 | 2 | 所有モジュール／名前空間から選ぶ 17599 宣言の推移的公理依存。sorryAx または証明本体の sorry |
| audit_adams_action_transport.lean | 通る | 0 | 4 | 1 | 0 | 0 | 明示の assert_no_sorry 4 命令。適用例: {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (τ : CochainCubicAction L) : (CochainCubicAction.comapIso … |
| audit_andre_initial_coefficient.lean | 通る | 673 | 673 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 673 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 20 命令。型指定: Nat.Prime.pos |
| audit_andre_unoriented.lean | 通る | 447 | 447 | 0 | 2 | 0 | 所有モジュール／名前空間から選ぶ 447 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。明示の assert_no_sorry 18 命令 |
| audit_bhatt_scholze.lean | 通る | 0 | 577 | 0 | 0 | 0 | 明示の assert_no_sorry 577 命令 |
| audit_bhatt_scholze_andre_conditional.lean | 通る | 0 | 1 | 0 | 0 | 0 | 明示の assert_no_sorry 1 命令 |
| audit_bhatt_scholze_arc_excision.lean | 通る | 0 | 0 | 2 | 0 | 0 | 型指定: BhattScholze.klCanonicalExcisionSquare_of_integral_away。適用例: (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (p : ℕ) [Fact p.Pri… |
| audit_bhatt_scholze_b4.lean | 通る | 0 | 2369 | 0 | 0 | 0 | 明示の assert_no_sorry 2369 命令 |
| audit_bhatt_scholze_b5.lean | 通る | 0 | 31 | 3 | 0 | 0 | 明示の assert_no_sorry 31 命令。型指定: _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension。適用例: (p : ℕ) [Fact p.Prime] : ∀ (A B C : Type u) [CommRi… |
| audit_bhatt_scholze_prop813.lean | 通る | 0 | 29 | 4 | 0 | 0 | 明示の assert_no_sorry 32 命令。型指定: hr.map。適用例: private lemma identityPerfectoidization (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (hA : IsIntegralPerfectoid A p) : IsP… |
| audit_bhatt_scholze_refactoring.lean | 通る | 0 | 190 | 49 | 0 | 0 | 明示の assert_no_sorry 190 命令。型指定: SerrePositivity.BhattScholze.rankOneDPPrimeBasis。適用例: noncomputable example (D : DeltaStructure p R) : relativeFreeDeltaSection σ D = MvP… |
| audit_bhatt_scholze_stage2.lean | 通る | 26608 | 26608 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 26608 宣言の推移的公理依存 |
| audit_citations.lean | 通る | 0 | 0 | 0 | 1 | 1 | 登録表と @[cite] のキーを照合。。登録済み文献キーと @[cite] を照合 |
| audit_clmst.lean | 通る | 0 | 938 | 0 | 0 | 0 | 明示の assert_no_sorry 944 命令 |
| audit_clmst_b3.lean | 通る | 0 | 82 | 6 | 0 | 0 | 明示の assert_no_sorry 82 命令。型指定: _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization。適用例: {R : Type} [CommRing R] (I : Ideal… |
| audit_coherent_nerve.lean | 通る | 0 | 0 | 0 | 0 | 2 | 印字: #check 234, axioms 234 |
| audit_derived_cell_projective.lean | 通る | 355 | 355 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 355 宣言の推移的公理依存 |
| audit_derived_closure_functoriality.lean | 通る | 770 | 770 | 0 | 0 | 41 | 所有モジュール／名前空間から選ぶ 770 宣言の推移的公理依存 |
| audit_derived_coherent_bar.lean | 通る | 1932 | 1932 | 0 | 2 | 6 | 所有モジュール／名前空間から選ぶ 1932 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出 |
| audit_derived_coherent_bar_compact.lean | 通る | 722 | 722 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 722 宣言の推移的公理依存 |
| audit_derived_coherent_bar_retract.lean | 通る | 529 | 529 | 0 | 0 | 1 | 所有モジュール／名前空間から選ぶ 529 宣言の推移的公理依存 |
| audit_derived_coherent_bar_strict.lean | 通る | 1798 | 1798 | 0 | 3 | 14 | 所有モジュール／名前空間から選ぶ 1798 宣言の推移的公理依存。宣言の種類・公開範囲の条件。監査モジュールの照合・実行漏れ検出 |
| audit_derived_dg_nerve_reflection.lean | 通る | 6 | 6 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_quasiEquivalence_of_nerve |
| audit_derived_gluing.lean | 通る | 11504 | 11504 | 0 | 2 | 142 | 所有モジュール／名前空間から選ぶ 11504 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出 |
| audit_derived_infinity.lean | 通る | 9362 | 9362 | 3 | 4 | 0 | 所有モジュール／名前空間から選ぶ 9362 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出。適用例: (S : Type u) [CommRing S] : SSet.Quasicategory (_root_.SerrePositivity.InfinityCategories.HA.De… |
| audit_derived_kappa_perfect.lean | 通る | 454 | 454 | 0 | 3 | 4 | 所有モジュール／名前空間から選ぶ 454 宣言の推移的公理依存。宣言の種類・公開範囲の条件。監査モジュールの照合・実行漏れ検出 |
| audit_derived_native_family.lean | 通る | 163 | 163 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 163 宣言の推移的公理依存 |
| audit_derived_native_p.lean | 通る | 62 | 62 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 62 宣言の推移的公理依存 |
| audit_derived_sphere_closure.lean | 通る | 51 | 51 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存 |
| audit_derived_suspension_coherent.lean | 通る | 43 | 43 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存 |
| audit_derived_suspension_native.lean | 通る | 23 | 23 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 23 宣言の推移的公理依存 |
| audit_derived_suspension_replacement.lean | 通る | 3 | 3 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 3 宣言の推移的公理依存 |
| audit_dg_cell_comparison.lean | 通る | 251 | 251 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 251 宣言の推移的公理依存 |
| audit_dg_nerve.lean | 通る | 0 | 0 | 7 | 0 | 0 | 適用例: (x y : D) (n : ℕ) : Module A (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) |
| audit_dg_perfect_projective_image.lean | 通る | 155 | 155 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 155 宣言の推移的公理依存。適用例: : ∀ (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D] (E : Type w) [DGCategory R E] [Small.{u} E] (T : DGFunctor… |
| audit_dg_projective_contraction.lean | 通る | 151 | 151 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 151 宣言の推移的公理依存。型指定: moduleHomotopicallyProjective_contractingElement_of_acyclic |
| audit_dg_quotient_parameter.lean | 通る | 644 | 644 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 644 宣言の推移的公理依存 |
| audit_dold_kan_comparison.lean | 通る | 0 | 0 | 0 | 0 | 3 | 印字: #check 645, axioms 645 |
| audit_einfinity.lean | 通る | 32390 | 32390 | 2205 | 0 | 0 | 所有モジュール／名前空間から選ぶ 32390 宣言の推移的公理依存。型指定: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionEquiv。適用例: : Function.Surjective b… |
| audit_euler_betti_finite_support.lean | 通る | 0 | 3 | 0 | 0 | 0 | 明示の assert_no_sorry 3 命令 |
| audit_euler_group_shared.lean | 通る | 0 | 9 | 0 | 0 | 0 | 明示の assert_no_sorry 11 命令 |
| audit_exact_euler_finite_support.lean | 通る | 0 | 4 | 0 | 0 | 0 | 明示の assert_no_sorry 4 命令 |
| audit_f2_compact.lean | 通る | 244 | 244 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 244 宣言の推移的公理依存 |
| audit_f2_ind.lean | 通る | 3910 | 3910 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 3910 宣言の推移的公理依存 |
| audit_f2_pi_criterion.lean | 通る | 225 | 225 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 225 宣言の推移的公理依存。型指定: SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.dgBarCompactFilteredSpacePiBridge |
| audit_f4.lean | 通る | 0 | 0 | 5 | 0 | 0 | 明示の assert_no_sorry 5 命令。型指定: exists_strictPRecoveryEquiv。適用例: theorem f4_audit_zero_ring (A : Type u) [CommRing A] [Subsingleton A] (p : ℕ) [Fact p.Prime] : ∃ e : WittV… |
| audit_f5.lean | 通る | 0 | 0 | 4 | 0 | 0 | 明示の assert_no_sorry 4 命令。適用例: theorem f5_audit_zero_bound (R : Type u) [CommRing R] (f : R) (M : ModuleCat.{u} R) (hM : IsModuleComplete R f M) (h0 : ∀ n : ℕ, ∀ x : M, f… |
| audit_f6.lean | 通る | 0 | 0 | 6 | 0 | 0 | 明示の assert_no_sorry 6 命令。型指定: perfection_lift_principal_quotient_kernel。適用例: theorem f6_audit_product_source_charP (k : Type u) [CommRing k] (p : ℕ) [CharP k p] : CharP … |
| audit_f7.lean | 通る | 0 | 0 | 3 | 0 | 0 | 明示の assert_no_sorry 3 命令。型指定: hS.fontaine_kernel_isHausdorff。適用例: theorem f7_audit_fontaine_comparison_surjective [IsPrecomplete (Ideal.span {d}) (WittVector p k)] (hd :… |
| audit_general_spectra.lean | 通る | 347 | 347 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 347 宣言の推移的公理依存 |
| audit_homotopical_foundations.lean | 通る | 7855 | 7855 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 7855 宣言の推移的公理依存 |
| audit_homotopical_general_tools.lean | 通る | 4763 | 4763 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 4763 宣言の推移的公理依存 |
| audit_homotopical_rectification.lean | 通る | 15112 | 15112 | 0 | 0 | 425 | 所有モジュール／名前空間から選ぶ 15112 宣言の推移的公理依存 |
| audit_homotopy_cone_representative_shared.lean | 通る | 0 | 6 | 0 | 0 | 0 | 明示の assert_no_sorry 6 命令 |
| audit_homotopy_limits.lean | 通る | 587 | 587 | 1 | 4 | 0 | 所有モジュール／名前空間から選ぶ 587 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_homotopy_property_shared.lean | 通る | 0 | 1 | 0 | 0 | 0 | 明示の assert_no_sorry 1 命令 |
| audit_infinity_accessible_pullback.lean | 通る | 672 | 672 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 672 宣言の推移的公理依存 |
| audit_infinity_core.lean | 通る | 1679 | 1679 | 4 | 4 | 0 | 所有モジュール／名前空間から選ぶ 1679 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出。型指定: _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialCofinality |
| audit_infinity_core_supply_s1_closed_stable.lean | 通る | 175 | 175 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 175 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_infinity_core_supply_s1_triangle.lean | 通る | 2 | 2 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 2 宣言の推移的公理依存。宣言型の禁止依存または sorry。型指定: _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext |
| audit_infinity_f1.lean | 通る | 20449 | 20449 | 1 | 4 | 19 | 所有モジュール／名前空間から選ぶ 20449 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_infinity_f1_f1b.lean | 通る | 0 | 0 | 0 | 2 | 0 | F1・F1B を同時 import し、各所有元の宣言が読まれたことを確認 |
| audit_infinity_f1b.lean | 通る | 5461 | 5461 | 1 | 2 | 0 | 所有モジュール／名前空間から選ぶ 5461 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_infinity_f2.lean | 通る | 10376 | 10376 | 2 | 0 | 157 | 所有モジュール／名前空間から選ぶ 10376 宣言の推移的公理依存。環境での宣言存在・型へのアクセス。型指定: _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasSpaceLimitsOfShape |
| audit_infinity_kan.lean | 通る | 30 | 30 | 1 | 2 | 0 | 所有モジュール／名前空間から選ぶ 30 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_infinity_model_bridge.lean | 通る | 85 | 85 | 1 | 2 | 0 | 所有モジュール／名前空間から選ぶ 85 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_infinity_presentable.lean | 通る | 6979 | 6979 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6979 宣言の推移的公理依存。型指定: hp.innerFibration |
| audit_infinity_presentable_duality.lean | 通る | 894 | 894 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 894 宣言の推移的公理依存 |
| audit_infinity_presentable_local_objects.lean | 通る | 24 | 24 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存 |
| audit_infinity_presentable_localization.lean | 通る | 1014 | 1014 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 1014 宣言の推移的公理依存。型指定: _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Generators.isLocalObject_ra… |
| audit_infinity_presentable_supply.lean | 通る | 726 | 726 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 726 宣言の推移的公理依存 |
| audit_infinity_sheaves.lean | 通る | 2387 | 2387 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 2387 宣言の推移的公理依存 |
| audit_infinity_stable.lean | 通る | 7002 | 7002 | 1 | 4 | 1 | 所有モジュール／名前空間から選ぶ 7002 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_infinity_stable_presentable.lean | 通る | 52 | 52 | 1 | 2 | 0 | 所有モジュール／名前空間から選ぶ 52 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_kst_cofinality.lean | 通る | 702 | 702 | 2 | 0 | 6 | 所有モジュール／名前空間から選ぶ 702 宣言の推移的公理依存。宣言型の禁止依存または sorry。適用例: : ∀ (X Y : SerrePositivity.KST.SConstruction.StableModel.{u}) (f : X ⟶ Y), SerrePositivity.InfinityCategories.Kero… |
| audit_kst_comparison.lean | 通る | 2209 | 2209 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 2209 宣言の推移的公理依存 |
| audit_kst_derived_blowup.lean | 通る | 3750 | 3750 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 3750 宣言の推移的公理依存 |
| audit_kst_derived_geometry.lean | 通る | 2636 | 2636 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 2636 宣言の推移的公理依存 |
| audit_kst_descent_main.lean | 通る | 1485 | 1485 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 1485 宣言の推移的公理依存 |
| audit_kst_fibration.lean | 通る | 4215 | 4215 | 1 | 0 | 74 | 所有モジュール／名前空間から選ぶ 4215 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_kst_fibration_relative.lean | 通る | 175 | 175 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 175 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_kst_nonconnective.lean | 通る | 2950 | 2950 | 1 | 0 | 124 | 所有モジュール／名前空間から選ぶ 2950 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_kst_s_construction_tail.lean | 通る | 95 | 95 | 1 | 2 | 3 | 所有モジュール／名前空間から選ぶ 95 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_kst_scheme_lemmas.lean | 通る | 12965 | 12965 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 12965 宣言の推移的公理依存 |
| audit_kst_spectra.lean | 通る | 13474 | 13474 | 2 | 2 | 5 | 所有モジュール／名前空間から選ぶ 13474 宣言の推移的公理依存。宣言型の禁止依存または sorry。監査モジュールの照合・実行漏れ検出 |
| audit_kst_spectra_d3.lean | 通る | 5598 | 5598 | 1 | 0 | 108 | 所有モジュール／名前空間から選ぶ 5598 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_kst_spectra_d3tail.lean | 通る | 4263 | 4263 | 3 | 0 | 3 | 所有モジュール／名前空間から選ぶ 4263 宣言の推移的公理依存。宣言型の禁止依存または sorry。型指定: nativeLoop_isQCatEquivalence_of_tailComparison |
| audit_kst_spectra_s3.lean | 通る | 24 | 24 | 1 | 0 | 4 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_local_algebra.lean | 通る | 0 | 702 | 0 | 0 | 0 | 明示の assert_no_sorry 705 命令 |
| audit_localizing_invariants.lean | 通る | 23726 | 23726 | 1 | 0 | 1273 | 所有モジュール／名前空間から選ぶ 23726 宣言の推移的公理依存。宣言型の禁止依存または sorry |
| audit_refactor_infinity.lean | 通る | 530 | 530 | 0 | 0 | 0 | 所有モジュール／名前空間から選ぶ 530 宣言の推移的公理依存 |
| audit_spectra.lean | 通る | 3014 | 3014 | 0 | 0 | 37 | 所有モジュール／名前空間から選ぶ 3014 宣言の推移的公理依存 |
| audit_stage4_contract.lean | 通る | 8533 | 8533 | 0 | 0 | 34 | 所有モジュール／名前空間から選ぶ 8533 宣言の推移的公理依存 |
| audit_triangulated_k0_shift_shared.lean | 通る | 0 | 2 | 0 | 0 | 0 | 明示の assert_no_sorry 2 命令 |

### manifest の外で失われる検査

同じ方法で非掲載から 311 本を抽出した。通る 148 本は手動で使える。
落ちる行にはソースが意図した検査を示す。手動・別入口の利用は CSV の `execution_callers` 欄に記録した。

<details>
<summary>非掲載の検査一覧</summary>

| scripts/ からのパス | 現状 | 公理 | sorry 残 | 型・適用例 | 構造 | 単独 import | 残る条件 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| check_accessible_cell_attachment.lean | 通る | 30 | 30 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 30 宣言の推移的公理依存。型指定: step_isCardinalAccessible |
| check_accessible_colimits.lean | 通る | 6 | 6 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: colimit_isCardinalAccessible |
| check_accessible_factorization_transport.lean | 通る | 41 | 41 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 41 宣言の推移的公理依存。型指定: arrowFunctor_isCardinalAccessible。適用例: [HasColimitsOfSize.{w, w} C] {L R : MorphismProperty C} (d : MorphismProperty.FunctorialFactor… |
| check_accessible_iteration.lean | 通る | 6 | 6 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: iterationStage_isCardinalAccessible |
| check_accessible_local_objects.lean | 落ちる | 15 | 15 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 15 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_accessible_smallLocalObjects_of_small |
| check_accessible_local_replacement.lean | 通る | 13 | 13 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 13 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: reedyLeft_inf_iff |
| check_accessible_mapping_tests.lean | 通る | 19 | 19 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 19 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_accessible_resolutionHom_family。適用例: (F : Cᵒᵖ ⥤ C ⥤ SSet.{v}) (f : Arrow C) (Y : C) : ((MappingTests.arrow F… |
| check_accessible_model_factorizations.lean | 通る | 55 | 55 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 55 宣言の推移的公理依存。型指定: exists_common_accessible_generated_factorizations。適用例: [ModelCategory C] [IsLocallyPresentable.{w} C] (I J : MorphismProperty C) [Ser… |
| check_accessible_reedy_boundary.lean | 通る | 17 | 17 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 17 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SerrePositivity.Smith.AccessibleAdjunction.rightAdjoint_isAccessible |
| check_accessible_resolutions.lean | 通る | 73 | 73 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 73 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialResolutionFamily_isAccessible。適用例: {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) : ∃ (κ : Cardinal.{w}) … |
| check_accessible_right_class.lean | 通る | 4 | 4 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 4 宣言の推移的公理依存。型指定: exists_accessible_right_lifting_class。適用例: [ModelCategory C] [IsLocallyPresentable.{w} C] (I J : MorphismProperty C) [SerrePositivity.… |
| check_accessible_small_object.lean | 通る | 7 | 7 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。型指定: locallyPresentable_hasColimits。適用例: [HasColimitsOfSize.{w, w} C] (I : MorphismProperty C) (μ : Cardinal.{w}) [Fact μ.IsRegular] [Order… |
| check_accessible_squares.lean | 通る | 46 | 46 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 46 宣言の推移的公理依存。型指定: DependentCopower.adjunction |
| check_actual_free_resolution_choices.lean | 落ちる | 38 | 38 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: OrdinaryBarFreeResolutionSeed.seed。適用例: : OrdinaryBarFreeResolutionChoices.diagram hcof hfib P 0 = OrdinaryBarFreeResolutionSeed.zero… |
| check_all_degree_free_generators.lean | 落ちる | 43 | 43 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。型指定: QuiverPaths.mapPath_intersection |
| check_all_factorization_choices.lean | 落ちる | 78 | 78 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 78 宣言の推移的公理依存。型指定: LargeParameterRelativeChoice.extension |
| check_all_factorization_comparison.lean | 落ちる | 33 | 33 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 33 宣言の推移的公理依存。型指定: UniverseLift.boundaryFillers |
| check_all_factorization_mixed.lean | 落ちる | 88 | 88 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 88 宣言の推移的公理依存。型指定: LargeParameterSquare.left_first |
| check_all_factorization_pre.lean | 落ちる | 18 | 18 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: LargeParameterMapping.fillers。適用例: (d : ℕ) (b : (SSet.boundary.{max w v} d).toSSet ⟶ (ihom K).obj (UniverseLift.obj.{w} P)) : (K ◁ (S… |
| check_all_factorization_small_action.lean | 落ちる | 64 | 64 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 64 宣言の推移的公理依存。型指定: NerveLargeSampling.family |
| check_ambient_word_comparison.lean | 通る | 10 | 10 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: AmbientWords.ambientHomEquiv |
| check_anchored_chain_comparison.lean | 落ちる | 94 | 94 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 94 宣言の推移的公理依存。型指定: c.cut_reindex |
| check_anchored_chain_contraction.lean | 落ちる | 16 | 16 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 16 宣言の推移的公理依存。型指定: NerveHomotopy.homotopy |
| check_anodyne_bar_comparison.lean | 通る | 31 | 31 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: endpoint_zero_anodyne。適用例: (d : D) : (spanLeftAnodyneIso p F).hom.app d = anodyneQ.map ((spanLeft p F).app d) |
| check_arbitrary_source_resolutions.lean | 通る | 108 | 108 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 108 宣言の推移的公理依存。型指定: ResolutionObject.hom_kanComplex。適用例: {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : ResolutionObject C) (f : X.base ⟶ Y.base… |
| check_balanced_resolution_comparison.lean | 通る | 68 | 68 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 68 宣言の推移的公理依存。型指定: BiresolutionRightMapping.rawFlipIso。適用例: (X : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) (f : ((BiresolutionRawMapping.f… |
| check_bisimplicial_cofibrancy.lean | 落ちる | 16 | 16 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 16 宣言の推移的公理依存。型指定: SerrePositivity.SimplicialLatching.comparison_mono |
| check_bousfield_detection.lean | 通る | 29 | 29 | 11 | 2 | 0 | 所有モジュール／名前空間から選ぶ 29 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SerrePositivity.SimplicialModel.piZero_bijective_of_trivialFibration |
| check_bousfield_locality.lean | 落ちる | 52 | 52 | 19 | 2 | 0 | 所有モジュール／名前空間から選ぶ 52 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: weakEquivalences_le_localEquivalences。適用例: : (localEquivalences cof fib S).HasTwoOutOfThreeProperty |
| check_choice_mapping_space.lean | 落ちる | 32 | 32 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 32 宣言の推移的公理依存。型指定: DiscreteFamily.exists_extension |
| check_coherent_lift_faces.lean | 落ちる | 4 | 4 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 4 宣言の推移的公理依存。適用例: {X P : SSet.{v}} {I : Type w} (A : X.Subcomplex) (U : I → X.Subcomplex) (hU : ⨆ i, U i = A) (f : ∀ i, (U i).toSSet ⟶ P) (hf : ∀ i j, S… |
| check_coherent_lift_tuples.lean | 通る | 57 | 57 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。型指定: CoherentLiftTuples.StrictLift。適用例: {X Y : ResolutionObject C} (g : X ⟶ Y) : SerrePositivity.InfinityCategories.Project.SimplicialComb… |
| check_colimit_frame.lean | 通る | 77 | 77 | 12 | 2 | 0 | 所有モジュール／名前空間から選ぶ 77 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: adjunctionHomIso。適用例: [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) (F… |
| check_comonad_resolution_presentation.lean | 通る | 54 | 54 | 15 | 0 | 0 | 所有モジュール／名前空間から選ぶ 54 宣言の推移的公理依存。型指定: face_face |
| check_comparison_coherence_restriction.lean | 落ちる | 0 | 0 | 5 | 0 | 1 | 型指定: ComparisonCoherenceRestriction.left_tetrahedron_family |
| check_comparison_tetrahedra.lean | 落ちる | 0 | 0 | 4 | 0 | 2 | 型指定: KanComparisonTetrahedron.coherence_zero。適用例: {T K : SSet.{v}} {f g h z : T ⟶ K} (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z) (a : Data F … |
| check_comparison_unit_triangles.lean | 落ちる | 4 | 4 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 4 宣言の推移的公理依存。型指定: BinaryIntervalTriangles.lower_comparison。適用例: {T K : SSet.{v}} {f g z : T ⟶ K} (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (a : Da… |
| check_compatible_horn_operation.lean | 落ちる | 0 | 0 | 6 | 0 | 2 | 型指定: CompatibleInputUnion.inputs。適用例: {J : Type u} (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (d : Fin (n + 1)) : CompatibleInputUnion.Compatible (fun _ : J => (ihom (SSet… |
| check_composition_choices.lean | 落ちる | 15 | 15 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 15 宣言の推移的公理依存。型指定: ComparisonTriangleChoices.boundary_rlp |
| check_composition_parameter_diagram.lean | 落ちる | 18 | 18 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: ComparisonTriangleParameterDiagram.diagram |
| check_composition_reindex.lean | 落ちる | 13 | 13 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 13 宣言の推移的公理依存。型指定: compositionChoices_reindex_id |
| check_continuous_projective_cofibrancy.lean | 通る | 101 | 101 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 101 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ContinuousLifts.exists_lift_with_base |
| check_derived_weak_inverse.lean | 通る | 26 | 26 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 26 宣言の推移的公理依存。適用例: {C : Type uC} [Category.{vC} C] [ModelCategory C] {D : Type uD} [Category.{vD} D] [ModelCategory D] {HC : Type uHC} [Category.{vHC} H… |
| check_diagonal_closed_action.lean | 落ちる | 18 | 18 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: ClosedParameterComposition.curry_comp |
| check_diagonal_closed_compatibility.lean | 落ちる | 32 | 32 | 14 | 0 | 0 | 所有モジュール／名前空間から選ぶ 32 宣言の推移的公理依存。型指定: ClosedParameterComposition.curry_comp |
| check_diagonal_hom_augmentation.lean | 通る | 51 | 51 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存。型指定: inclusion_transfer |
| check_diagonal_internal_hom.lean | 通る | 30 | 30 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 30 宣言の推移的公理依存。型指定: restrictedRepresentableIso |
| check_diagonal_lift_actions.lean | 落ちる | 51 | 51 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存。型指定: DiagonalHom.composition |
| check_diagonal_localized_equivalence.lean | 落ちる | 21 | 21 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 21 宣言の推移的公理依存。型指定: KanLocalizedMonoLifting.hasLiftingProperty |
| check_diagonal_weak_equivalences.lean | 落ちる | 40 | 40 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 40 宣言の推移的公理依存。型指定: matchingOpEquivalence。適用例: {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = M… |
| check_diagonal_word_evaluation.lean | 落ちる | 0 | 0 | 12 | 0 | 0 | 型指定: OrdinaryBarFixedSource.literal。適用例: {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C) : ((OrdinaryBarFixedSource.literal C).map θ).toFunctor.obj X = X |
| check_enriched_detection.lean | 通る | 52 | 52 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 52 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: original。適用例: (P : SerrePositivity.Enriched.TensorCotensor SSet.{vC} D) (hcof : cofibrations SSet.{vC} = MorphismPr… |
| check_enriched_localization.lean | 通る | 9 | 9 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 9 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。適用例: {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S) (hdom : ∀ {A B : V} (i : A ⟶ B), IV i → IsCofibrant… |
| check_enriched_localization_existence.lean | 通る | 2 | 2 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 2 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_enriched_localization。適用例: (S : MorphismProperty C) [S.IsSmall.{w}] (hcompat : ∀ {A B : SSet.{v}} (i : A ⟶ B)… |
| check_enriched_tensor_cotensor.lean | 通る | 0 | 0 | 8 | 0 | 0 | 型指定: S.homEquiv_compatibility。適用例: [IsQuillenBifunctor S.tensor] (K : V) [IsCofibrant K] : IsLeftQuillen (S.tensor.obj K) ∧ IsRightQuillen (S.cotensor.obj (op K)) |
| check_factorization_external_transport.lean | 落ちる | 70 | 70 | 15 | 0 | 0 | 所有モジュール／名前空間から選ぶ 70 宣言の推移的公理依存。型指定: ArrowFactorization.transport_forget。適用例: : AllFactorizationPost.direct hcof hfib f g b = AnchoredChain.mapFunctor (ArrowFactorization… |
| check_factorization_nerve.lean | 通る | 120 | 120 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 120 宣言の推移的公理依存。型指定: ArrowFactorization.source_isInitial。適用例: {i j : Fin (n + 1)} (h : i ⟶ j) : (AnchoredChain.fromDiagram F).diagram.map h = (F.map h).h… |
| check_filtered_homotopy_colimit.lean | 通る | 35 | 35 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 35 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: HomotopyColimit.exists_filtered_comparison |
| check_finite_chain_cube.lean | 落ちる | 43 | 43 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。型指定: ParameterCube.face_coordinate_same |
| check_finite_tensor_cells.lean | 通る | 24 | 24 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: FiniteTensor.coproductIso |
| check_finite_tensor_generic.lean | 通る | 46 | 46 | 8 | 2 | 0 | 所有モジュール／名前空間から選ぶ 46 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: FiniteTensor.functor。適用例: {n : SimplexCategory} {S T : (SSet.stdSimplex.{v}.obj n).Subcomplex} (h : S ≤ T) : Subcom… |
| check_finite_tensor_lifting.lean | 落ちる | 107 | 107 | 10 | 2 | 0 | 所有モジュール／名前空間から選ぶ 107 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SubcomplexTensor.homEquiv。適用例: (n : ℕ) (i : Fin (n + 1)) : HasColimit (SubcomplexTensor.diagram (SSet.horn.{v} n i… |
| check_frame_realization.lean | 落ちる | 44 | 44 | 9 | 2 | 0 | 所有モジュール／名前空間から選ぶ 44 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: Realization.adjunction |
| check_frame_right_quillen.lean | 通る | 16 | 16 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 16 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialHom_isRightQuillen |
| check_framed_mapping_bifunctor.lean | 通る | 118 | 118 | 15 | 0 | 0 | 所有モジュール／名前空間から選ぶ 118 宣言の推移的公理依存。型指定: FramedResolution.liftBase_base。適用例: : (FramedResolution.forget (C := C)).Full |
| check_framed_pre_choice_functor.lean | 通る | 47 | 47 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 47 宣言の推移的公理依存。型指定: RelativeChoiceFunctor.functor |
| check_free_chain_transfer.lean | 落ちる | 0 | 0 | 10 | 0 | 0 | 型指定: ofPath_length |
| check_free_chain_units.lean | 落ちる | 10 | 10 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: contraction_one_right |
| check_free_latching_extension.lean | 通る | 50 | 50 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 50 宣言の推移的公理依存。型指定: values_agree |
| check_free_path_comonad.lean | 落ちる | 7 | 7 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。型指定: FreePathResolution.counit_naturality |
| check_free_resolution_action.lean | 落ちる | 0 | 0 | 11 | 0 | 0 | 型指定: action_naturality |
| check_free_resolution_boundary_data.lean | 落ちる | 35 | 35 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 35 宣言の推移的公理依存。型指定: face_comparison。適用例: (n : ℕ) (i : Fin (n + 1)) (X : D) : (fixedFace D n i).obj X = X |
| check_free_resolution_natural_choices.lean | 落ちる | 15 | 15 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 15 宣言の推移的公理依存。型指定: SimplexNaturality.naturality。適用例: (n : SimplexCategoryᵒᵖ) : (SimplexNaturality.ofFacesDegeneracies F G a hδ hσ).app n = a n |
| check_free_resolution_step.lean | 落ちる | 0 | 0 | 12 | 0 | 0 | 型指定: degeneracy_face_self。適用例: : OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A 0 = A.previous |
| check_free_triangle_boundary.lean | 通る | 49 | 49 | 25 | 0 | 0 | 所有モジュール／名前空間から選ぶ 49 宣言の推移的公理依存。型指定: faceOne_lowerZero |
| check_free_triangle_gluing.lean | 通る | 50 | 50 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 50 宣言の推移的公理依存。型指定: BoundaryTensorGluing.desc_fac |
| check_free_word_hom.lean | 落ちる | 6 | 6 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: normalFormEquiv |
| check_general_spectra.lean | 通る | 0 | 0 | 27 | 0 | 0 | 型指定: freeForgetAdjunction。適用例: : Category (GeneralSymmetricSpectrum C K) |
| check_general_spectrum_internal_hom_omega.lean | 落ちる | 26 | 26 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 26 宣言の推移的公理依存。型指定: InternalHomExchange.iso |
| check_general_spectrum_level_monoidal.lean | 落ちる | 26 | 26 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 26 宣言の推移的公理依存。型指定: m |
| check_general_tensor_cotensor.lean | 通る | 341 | 341 | 44 | 0 | 0 | 所有モジュール／名前空間から選ぶ 341 宣言の推移的公理依存。型指定: pointwiseTensor_level。適用例: (E F : GeneralSymmetricSpectrum C K) : (E ⟶[C] F) = mappingObject E F |
| check_generated_bifunctor.lean | 落ちる | 1 | 1 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 1 宣言の推移的公理依存。型指定: isQuillenBifunctor_of_generators。適用例: : HasQuillenPullbackHom G |
| check_hocolim_local_equivalences.lean | 通る | 9 | 9 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 9 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: HocolimSourceTests.smallLocalEquivalence_hocolim |
| check_hocolim_mapping_comparison.lean | 通る | 34 | 34 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 34 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: WeightedHomotopyColimitFrame.augmentation_weakEquivalence |
| check_hocolim_rmap_formula.lean | 通る | 63 | 63 | 8 | 2 | 0 | 所有モジュール／名前空間から選ぶ 63 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: HocolimRMapFormula.fromSource_weakEquivalence。適用例: (D : (K ⥤ C)ᵒᵖ) (Y : C) : ((HocolimRMapFormula.source K I J cof … |
| check_hocolim_weighted_comparison.lean | 通る | 21 | 21 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 21 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SmallHomFrameWeights.standardFrameHomFamilyIso |
| check_hom_parameter_descent.lean | 落ちる | 37 | 37 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: OrdinaryBarHomSections.source |
| check_homotopical_derived.lean | 通る | 0 | 0 | 18 | 0 | 0 | 型指定: map_weakEquivalence_of_cofibrant。適用例: (L : C ⥤ D) [IsLeftQuillen L] : (L ⋙ QD).HasPointwiseLeftDerivedFunctor (weakEquivalences C) |
| check_homotopical_foundations.lean | 通る | 0 | 0 | 27 | 0 | 0 | 型指定: isRightQuillen_of_isLeftQuillen。適用例: : IsLeftQuillen (𝟭 C) |
| check_homotopical_monoidal.lean | 通る | 0 | 0 | 9 | 0 | 0 | 型指定: isQuillenBifunctor_iff_pullbackHom。適用例: [IsQuillenBifunctor F] : IsQuillenBifunctor F.flip |
| check_homotopical_transfer.lean | 落ちる | 0 | 0 | 11 | 0 | 0 | 型指定: cofibrations_eq_generated。適用例: : let m |
| check_homotopy_generators.lean | 通る | 15 | 15 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 15 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。適用例: (cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) (fib₁ fib₂ : Morp… |
| check_homotopy_limit.lean | 通る | 61 | 61 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 61 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: WeightedCones.adjunction |
| check_homotopy_suspension.lean | 落ちる | 73 | 73 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 73 宣言の推移的公理依存。型指定: p.localization.generators。適用例: {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C] [HasZeroMorphisms C] {X : C} [IsCofi… |
| check_horn_family_lifting.lean | 落ちる | 0 | 0 | 6 | 0 | 1 | 型指定: KanHornFamilyLifting.relativeFamily_earlier。適用例: : ∃ e : V ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K, j ≫ e = a ∧ e ≫ KanHornFamilyLifting.r… |
| check_iterated_localization.lean | 通る | 8 | 8 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 8 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_iterated_localization |
| check_kan_cube_coproduct.lean | 通る | 10 | 10 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: KanPushoutCube.localized_isIso |
| check_kan_lift_actions.lean | 落ちる | 36 | 36 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 36 宣言の推移的公理依存。型指定: KanLiftAction.piZeroLocalizationEquiv。適用例: [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)… |
| check_kan_lift_coherence.lean | 落ちる | 37 | 37 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: KanLiftCoherence.boundary_extension。適用例: {X Y : ResolutionObject C} (f : X ⟶ Y) : ∃ H : ∀ Z : C, SSet.stdSimplex.{v}.obj (SimplexCate… |
| check_kan_localized_left_proper.lean | 通る | 29 | 29 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 29 宣言の推移的公理依存。型指定: PrecompositionHomotopy.homotopy |
| check_kan_localized_representatives.lean | 落ちる | 23 | 23 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 23 宣言の推移的公理依存。型指定: KanLocalizedRepresentatives.representative_map |
| check_kan_mono_extension.lean | 通る | 12 | 12 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 12 宣言の推移的公理依存。型指定: KanMonoEndpointExtension.exists_from_zero |
| check_kan_pullback_deformation.lean | 通る | 5 | 5 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 5 宣言の推移的公理依存。型指定: KanFibrationEndpointExtension.exists_from_zero |
| check_kan_pushout_comparison.lean | 通る | 20 | 20 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 20 宣言の推移的公理依存。型指定: MonoRightLiftingContraction.exists_section |
| check_kan_pushout_equivalence.lean | 通る | 46 | 46 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 46 宣言の推移的公理依存。型指定: KanActualHomotopy.of_class_eq |
| check_kan_quillen_level.lean | 落ちる | 17 | 17 | 15 | 0 | 2 | 所有モジュール／名前空間から選ぶ 17 宣言の推移的公理依存。sorryAx または証明本体の sorry。型指定: pointedSimplicial_monoidalModel。適用例: {X Y : SSet.{u}} (f : X ⟶ Y) : WeakEquivalence f ↔ geometricWeakEquivalen… |
| check_kan_quillen_resolution_hom.lean | 落ちる | 146 | 146 | 3 | 0 | 2 | 所有モジュール／名前空間から選ぶ 146 宣言の推移的公理依存。sorryAx または証明本体の sorry。型指定: resolutionHom_target_geometricWeakEquivalence |
| check_kan_retraction_lifting.lean | 落ちる | 28 | 28 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 28 宣言の推移的公理依存。型指定: KanTwoHornLift.exists_triangle |
| check_kan_sequential_comparison.lean | 通る | 103 | 103 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 103 宣言の推移的公理依存。型指定: BoundaryRightColimit.sequential_rlp。適用例: (n : ℕ) : KanTestLiftingClass.rightTests.llp (MonoLocalizedFactorization.left (successorArr… |
| check_kan_test_detection.lean | 通る | 24 | 24 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存。型指定: AnodyneKanReplacement.unit_anodyne |
| check_kan_transfinite_equivalence.lean | 通る | 28 | 28 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 28 宣言の推移的公理依存。型指定: localizedMonos_eq。適用例: : MorphismProperty.IsStableUnderTransfiniteComposition.{max u v} localizedMonos.{max u v} |
| check_left_proper_pushout.lean | 通る | 7 | 7 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SerrePositivity.UnderModel.pushout_map_weakEquivalence。適用例: {X Y : C} (f : X ⟶ Y) : SerrePositivity.Quillen.IsLeftQu… |
| check_level_enriched.lean | 通る | 35 | 35 | 16 | 0 | 0 | 所有モジュール／名前空間から選ぶ 35 宣言の推移的公理依存。型指定: GeneralSymmetricSpectrum.pointwiseTensor_isQuillen |
| check_lift_postcomposition.lean | 落ちる | 31 | 31 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: ResolutionLiftPostcomposition.ofLift。適用例: (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) {K L : SSet.{v}} (i : K ⟶ L)… |
| check_lift_precomposition.lean | 落ちる | 55 | 55 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 55 宣言の推移的公理依存。型指定: LiftSpacePrecomposition.map。適用例: {X Y : ResolutionObject C} (f : X ⟶ Y) (Z : C) [IsFibrant Z] (hf : weakEquivalences C f.base) : ∃ t … |
| check_lift_transport_laws.lean | 落ちる | 78 | 78 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 78 宣言の推移的公理依存。型指定: RelativeChoiceSpace.family_preMap。適用例: {V T P Q K L : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q) (q : P ⟶ Q) (hq : b ≫ q = b') (j… |
| check_local_fibrant_approximation.lean | 通る | 49 | 49 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 49 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ArrowFrames.inclusion_reedyCofibration。適用例: (f : Arrow C) (n : SimplexCategory) : weakEquivalences C (ArrowFrames.d… |
| check_local_presentable_cover.lean | 通る | 22 | 22 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 22 宣言の推移的公理依存。型指定: h.isCardinalAccessibleCategory。適用例: : LocalPresentableCover (⊤ : ObjectProperty C) κ where cover _ A _ f |
| check_local_replacement_detection.lean | 通る | 62 | 62 | 7 | 2 | 0 | 所有モジュール／名前空間から選ぶ 62 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ArrowLiftingClass.mem_iff |
| check_local_replacement_universal.lean | 通る | 60 | 60 | 14 | 2 | 0 | 所有モジュール／名前空間から選ぶ 60 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_accessible_localReplacementData。適用例: (X : C) : weakEquivalences C (d.η.app (d.L.obj X)) ∧ weakEquivalences C… |
| check_localization_left_proper_closure.lean | 通る | 17 | 17 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 17 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: localEquivalences_leftProperClosure。適用例: (S : MorphismProperty C) (K : Type w) [LinearOrder K] [OrderBot K] [SuccOr… |
| check_localization_model_existence.lean | 通る | 31 | 31 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: exists_modelPresentation。適用例: (S : MorphismProperty C) [S.IsSmall.{w}] : IsLocalizationModel.{v, u} cof fib S (mode… |
| check_localization_quillen_universal.lean | 通る | 10 | 10 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: original。適用例: : @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations m.categoryWithWeakEquivalences target.cat… |
| check_many_object_presentability.lean | 落ちる | 13 | 13 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 13 宣言の推移的公理依存。型指定: modelCategoryOfPresentableGenerators |
| check_many_object_transfer.lean | 落ちる | 9 | 9 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 9 宣言の推移的公理依存。型指定: modelCategoryOfTensorFormula。適用例: : @weakEquivalences D _ (modelCategoryOfTensorFormula L R I J adj H e).categoryWithWeakEquivalences … |
| check_mapping_limit.lean | 通る | 30 | 30 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 30 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: MappingLimit.coneIsLimit |
| check_mixed_center_chain_action.lean | 落ちる | 54 | 54 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 54 宣言の推移的公理依存。型指定: MixedResolutionCenters.action_transport |
| check_mixed_choice_compatibility.lean | 落ちる | 56 | 56 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 56 宣言の推移的公理依存。型指定: RelativeChoiceSpace.postIso |
| check_mixed_choice_functor.lean | 落ちる | 47 | 47 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 47 宣言の推移的公理依存。型指定: FiberFunctor.functor |
| check_mixed_lift_action_weak_equivalence.lean | 落ちる | 25 | 25 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 25 宣言の推移的公理依存。型指定: SerrePositivity.Quillen.ContractibleParameters.graph_weakEquivalence |
| check_mixed_resolution_comparison.lean | 通る | 57 | 57 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。型指定: MixedResolutionComparison.augmentation_weakEquivalence。適用例: (X : RightResolutionMapping.Index C) : weakEquivalences SSet.{v} ((MixedR… |
| check_mixed_resolution_lift_action.lean | 落ちる | 87 | 87 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 87 宣言の推移的公理依存。型指定: MixedDiagonalHom.pre_post |
| check_model_free_bar.lean | 通る | 31 | 31 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: functor |
| check_model_replacement.lean | 落ちる | 20 | 20 | 4 | 0 | 2 | 所有モジュール／名前空間から選ぶ 20 宣言の推移的公理依存。適用例: : ∃ Q : C ⥤ C, ∃ q : Q ⟶ 𝟭 C, ∀ X, IsCofibrant (Q.obj X) ∧ trivialFibrations C (q.app X) |
| check_model_saturation.lean | 通る | 9 | 9 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 9 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: weakEquivalences_iff_isIso_map |
| check_module_model_transfer.lean | 落ちる | 0 | 0 | 8 | 0 | 0 | 型指定: moduleModelCategory |
| check_monoid_axiom.lean | 通る | 18 | 18 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: tensor_trivialCofibration_weakEquivalence |
| check_monoidal_level_model.lean | 落ちる | 58 | 58 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 58 宣言の推移的公理依存。型指定: levelModelCategoryOfMonoidalGenerators。適用例: (n m : ℕ) : Quiver.IsThin (CostructuredArrow (FiniteBijection.addRight n) (FiniteBijectio… |
| check_monoidal_localization.lean | 通る | 3 | 3 | 2 | 2 | 0 | 所有モジュール／名前空間から選ぶ 3 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。適用例: {S : MorphismProperty C} (p : ModelPresentation.{w} cof fib I S) (hF : @SerrePositivity.Quillen.IsQuillenBifunctor C… |
| check_moving_choice_chain_transfer.lean | 落ちる | 34 | 34 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 34 宣言の推移的公理依存。型指定: RetractChainFamily.zero_family_face |
| check_native_associativity_coherence.lean | 落ちる | 98 | 98 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 98 宣言の推移的公理依存。型指定: left_first |
| check_native_unit_coherence.lean | 落ちる | 69 | 69 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 69 宣言の推移的公理依存。型指定: left_first |
| check_nerve_boundary_extension.lean | 通る | 146 | 146 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 146 宣言の推移的公理依存。型指定: NerveBoundaryExtension.extend_evaluate |
| check_nerve_coherent_extension.lean | 通る | 73 | 73 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 73 宣言の推移的公理依存。型指定: SimplexMatchingTerminal.exists_terminal。適用例: : Nonempty (NerveCoherentFamily.System (HomotopyFunctionComplex.MixedChoiceFunctor.funct… |
| check_nerve_coherent_family.lean | 落ちる | 42 | 42 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 42 宣言の推移的公理依存。型指定: Reedy.elementsReedy。適用例: {x y : D} (f : x ⟶ y) : endpointMap (reindexArrow (ComposableArrows.mk₁ f) (SimplexCategory.δ (1 : Fin 2))) … |
| check_nerve_cylinder_extension.lean | 落ちる | 57 | 57 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。型指定: NerveBiparameterMaps.reindex |
| check_nerve_interval_boundary.lean | 通る | 116 | 116 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 116 宣言の推移的公理依存。型指定: NerveIntervalBoundary.betweenChosen_evaluate |
| check_nerve_large_parameter.lean | 落ちる | 80 | 80 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 80 宣言の推移的公理依存。型指定: NerveMonomorphismLifting.extend_boundary |
| check_nerve_lower_extension.lean | 通る | 45 | 45 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 45 宣言の推移的公理依存。型指定: NerveLowerExtension.extend_restrict。適用例: private lemma hp (t : MixedChoiceFunctor.Context Y W) : trivialFibrations SSet.{v} ((NerveCo… |
| check_nerve_moving_parameter.lean | 落ちる | 73 | 73 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 73 宣言の推移的公理依存。型指定: NerveMovingParameter.extendFamilies_evaluate。適用例: {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) : (ResolutionArrowParameters.par… |
| check_nerve_parameter_extension.lean | 通る | 42 | 42 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 42 宣言の推移的公理依存。型指定: NerveRelativeValueExtension.extend_boundary。適用例: private lemma hp (t : MixedChoiceFunctor.Context Y W) : trivialFibrations SSet.{v} (… |
| check_nerve_prescribed_cells.lean | 通る | 38 | 38 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: cells.assemble_restrict。適用例: {x y : D} (f : x ⟶ y) : (whole F hp hcof points edges triangles).app (ofChain (ComposableArrows.mk₁ f)) … |
| check_normalized_comparison_coherence.lean | 落ちる | 0 | 0 | 8 | 0 | 1 | 型指定: NormalizedComparisonTetrahedron.build |
| check_normalized_horn_filling.lean | 落ちる | 9 | 9 | 8 | 0 | 1 | 所有モジュール／名前空間から選ぶ 9 宣言の推移的公理依存。型指定: CosimplicialDegenerateHorn.eq_of_faces |
| check_normalized_horn_target_coherence.lean | 落ちる | 0 | 0 | 14 | 0 | 1 | 型指定: CompatibleInputMap.map。適用例: : _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ NormalizedHornTargetComposition.triangle i hK hL hM q r = (NormalizedHornTargetComparison.comparis… |
| check_normalized_horn_target_comparison.lean | 落ちる | 6 | 6 | 7 | 0 | 1 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy。適用例: (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) : SSet.Hom… |
| check_normalized_native_triangles.lean | 落ちる | 19 | 19 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 19 宣言の推移的公理依存。型指定: NormalizedTriangleHorn.section_degeneracy |
| check_ordinary_bar_endpoints.lean | 落ちる | 31 | 31 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: SerrePositivity.LabelledChain.reconstruct |
| check_ordinary_bar_evaluation.lean | 落ちる | 91 | 91 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 91 宣言の推移的公理依存。型指定: OrdinaryBarEvaluation.evaluation。適用例: : OrdinaryBarEvaluation.bar R = (OrdinaryResolutionBar.functor (C := C)).obj ((RightResolutionM… |
| check_ordinary_bar_evaluation_equivalence.lean | 通る | 37 | 37 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: SimplexNerve.map_localized_isIso |
| check_ordinary_bar_homotopy_descent.lean | 落ちる | 17 | 17 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 17 宣言の推移的公理依存。型指定: X |
| check_ordinary_bar_label_surjectivity.lean | 落ちる | 8 | 8 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 8 宣言の推移的公理依存。型指定: OrdinaryBarLabelSurjectivity.raw_label_surjective |
| check_ordinary_bar_mapping_classes.lean | 落ちる | 50 | 50 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 50 宣言の推移的公理依存。型指定: LocalizedHomDiagram.equiv |
| check_ordinary_bar_mapping_comparison.lean | 通る | 21 | 21 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 21 宣言の推移的公理依存。型指定: OrdinaryBarMappingComparison.zeroIso |
| check_ordinary_bar_nerve_bridge.lean | 落ちる | 51 | 51 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存。型指定: SimplexNerveAugmentation.augmentation |
| check_ordinary_bar_pi_zero.lean | 落ちる | 41 | 41 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 41 宣言の推移的公理依存。型指定: PiZeroConstant.homEquiv |
| check_ordinary_bar_retract_system.lean | 落ちる | 45 | 45 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 45 宣言の推移的公理依存。型指定: LocalizedRelativeChoice.boundary_rlp |
| check_ordinary_bar_small_reference.lean | 落ちる | 25 | 25 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 25 宣言の推移的公理依存。型指定: toReference_isIso |
| check_ordinary_bar_total_cone.lean | 落ちる | 37 | 37 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: SerrePositivity.NerveHomotopyUniverse.homotopy |
| check_ordinary_kan_bar_mapping_classes.lean | 通る | 27 | 27 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 27 宣言の推移的公理依存。型指定: DiscreteKanExtension.naturalExtension_fac |
| check_ordinary_kan_bar_quotient.lean | 落ちる | 51 | 51 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存。型指定: DiscreteLocalizedExtension.descend_fac |
| check_ordinary_quotient_pi_zero.lean | 落ちる | 12 | 12 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 12 宣言の推移的公理依存。型指定: UniverseLiftPiZero.equiv |
| check_ordinary_resolution_bar.lean | 通る | 37 | 37 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: BarConstruction.reindex |
| check_ordinary_resolution_bar_reduction.lean | 通る | 22 | 22 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 22 宣言の推移的公理依存。型指定: BarConstruction.middleReindexImageIso |
| check_ordinary_suspension_stability.lean | 落ちる | 87 | 87 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 87 宣言の推移的公理依存。型指定: pointedSimplicial_isLocallyPresentable |
| check_parameter_choice_category.lean | 通る | 83 | 83 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 83 宣言の推移的公理依存。型指定: ParameterCategory.reindex_comp。適用例: (T : SSet.{w}) : Category.{w} (ParameterCategory.Object T) |
| check_parameterized_horn_choices.lean | 落ちる | 0 | 0 | 6 | 0 | 1 | 型指定: ParameterizedHornChoices.family_face。適用例: private lemma tetrahedronFaces {T K : SSet.{v}} {f g h z : T ⟶ K} (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSe… |
| check_pointed_model.lean | 通る | 63 | 63 | 16 | 0 | 0 | 所有モジュール／名前空間から選ぶ 63 宣言の推移的公理依存。型指定: cofibration_iff_underlying |
| check_pointwise_mapping_diagram.lean | 通る | 45 | 45 | 7 | 2 | 0 | 所有モジュール／名前空間から選ぶ 45 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: EvaluatedFrame.reedyCofibrant。適用例: [ModelCategory SSet.{v}] (hcof : cofibrations SSet.{v} = MorphismProperty.monomo… |
| check_post_chain_reindexing.lean | 落ちる | 35 | 35 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 35 宣言の推移的公理依存。型指定: TriangleBook.reindex_comp |
| check_post_choice_functor.lean | 落ちる | 56 | 56 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 56 宣言の推移的公理依存。型指定: HomotopyEndpointComparison.homotopy。適用例: {G H : Under Y} (p : G ⟶ H) : (PostChoiceFunctor.point hcof f).app G ≫ (PostChoiceFunctor.fu… |
| check_post_composition_chain.lean | 落ちる | 65 | 65 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 65 宣言の推移的公理依存。型指定: PostCompositionChain.prefix_suffix。適用例: (i : Fin (n + 1)) : PostCompositionChain.cutTriangle hcof hfib F X f i = CoherentLiftPostComp… |
| check_presentable_weak_reflection.lean | 通る | 44 | 44 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 44 宣言の推移的公理依存。型指定: presentable_of_accessible_fullyFaithful |
| check_presentation_kernel_quotient.lean | 落ちる | 18 | 18 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: SmallTargetKernelQuotient.factorization |
| check_projective_bifunctor.lean | 通る | 61 | 61 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 61 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SerrePositivity.PointwiseAdjunction.adjunction。適用例: (G : Vᵒᵖ ⥤ C ⥤ C) {A B : V} (i : A ⟶ B) {X Y : K ⥤ C} (p : X ⟶ … |
| check_projective_cofibrations.lean | 通る | 7 | 7 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: Projective.cofibration_app |
| check_projective_diagram_model.lean | 通る | 29 | 29 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 29 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: Projective.modelCategory。適用例: : Nonempty (ModelCategory (K ⥤ C)) |
| check_quillen_fibrant_criterion.lean | 通る | 8 | 8 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 8 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: Quillen.weakEquivalence_of_lifts_fibrant_fibrations。適用例: : @Quillen.IsLeftQuillen C _ D _ m.categoryWithCofibrations… |
| check_recursive_choice_extension.lean | 落ちる | 29 | 29 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 29 宣言の推移的公理依存。型指定: SerrePositivity.SequentialExtension.stage_map。適用例: (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗ K ⟶ (cosimplicialHom Y.resolution.obj)… |
| check_reedy_diagram_tower.lean | 通る | 199 | 199 | 15 | 2 | 0 | 所有モジュール／名前空間から選ぶ 199 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: T.toFunctor。適用例: [ModelCategory C] {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) : MorphismProperty.MapFactorizationData… |
| check_reedy_extension.lean | 通る | 232 | 232 | 15 | 2 | 0 | 所有モジュール／名前空間から選ぶ 232 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: lowerReedy |
| check_reedy_functor_data.lean | 通る | 37 | 37 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: d.toFunctor |
| check_reedy_functorial_extension.lean | 通る | 200 | 200 | 13 | 2 | 0 | 所有モジュール／名前空間から選ぶ 200 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: FactorizationProblem.relativeBoundaryFunctor。適用例: [ModelCategory C] (source : MorphismProperty.FunctorialFactoriza… |
| check_reedy_lifting.lean | 通る | 63 | 63 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 63 宣言の推移的公理依存。型指定: Lifting.hasLiftingProperty。適用例: {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) : ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b |
| check_reedy_lifting_step.lean | 通る | 31 | 31 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: LiftingStep.square。適用例: [HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)] : ∃ l : B.obj j ⟶ X.obj j, i.app… |
| check_reedy_lower_boundary.lean | 通る | 38 | 38 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: ι_lowerBoundary_π |
| check_reedy_model_category.lean | 通る | 34 | 34 | 8 | 2 | 0 | 所有モジュール／名前空間から選ぶ 34 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: simplexModelCategory |
| check_reedy_nested_boundaries.lean | 落ちる | 134 | 134 | 12 | 2 | 0 | 所有モジュール／名前空間から選ぶ 134 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: matchingNestedEquivalence |
| check_reedy_objects.lean | 通る | 57 | 57 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。型指定: latching_degree_lt |
| check_reedy_relative_arrows.lean | 落ちる | 142 | 142 | 15 | 2 | 0 | 所有モジュール／名前空間から選ぶ 142 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: relativeLatchingArrow。適用例: [ModelCategory C] : (reedyLeft simplex (cofibrations C)).IsStableUnderRetracts |
| check_reedy_resolution.lean | 通る | 145 | 145 | 12 | 2 | 0 | 所有モジュール／名前空間から選ぶ 145 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialResolution |
| check_reedy_simplex_finite.lean | 通る | 34 | 34 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 34 宣言の推移的公理依存。型指定: latchingComparison。適用例: (j : SimplexCategory) : FinCategory (LatchingIndex simplex j) |
| check_relative_bar_diagonal_contraction.lean | 落ちる | 17 | 17 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 17 宣言の推移的公理依存。型指定: contractionInterval_operator |
| check_relative_bar_span.lean | 落ちる | 31 | 31 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: UniverseLift.iterationIso |
| check_relative_boundary_filling.lean | 落ちる | 6 | 6 | 3 | 0 | 1 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: RelativeProductLifting.exists_lift |
| check_relative_choice_composition.lean | 落ちる | 24 | 24 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存。型指定: RelativeChoiceSpace.familyEquiv |
| check_relative_composition.lean | 落ちる | 55 | 55 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 55 宣言の推移的公理依存。型指定: ClosedHomotopyComposition.assoc_interval |
| check_relative_free_diagram_extension.lean | 通る | 74 | 74 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 74 宣言の推移的公理依存。型指定: OrdinaryBarFreeDiagramExtension.extendFunctor_restriction |
| check_relative_free_resolution_comparison.lean | 通る | 69 | 69 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 69 宣言の推移的公理依存。型指定: OrdinaryBarFreeDiagramHomotopy.comparison_zero |
| check_relative_free_triangle_filler.lean | 落ちる | 53 | 53 | 16 | 0 | 0 | 所有モジュール／名前空間から選ぶ 53 宣言の推移的公理依存。型指定: FreePathDegeneracyImage.generator_image_intersection |
| check_relative_hocolim.lean | 通る | 58 | 58 | 7 | 2 | 0 | 所有モジュール／名前空間から選ぶ 58 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: BottomReplacement.comparison_change |
| check_relative_hom_descent.lean | 落ちる | 28 | 28 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 28 宣言の推移的公理依存。型指定: KanRestrictionEquivalence.localized_isIso |
| check_relative_horn_operation.lean | 落ちる | 0 | 0 | 7 | 0 | 2 | 型指定: RelativeHornFillingOperation.section_restriction。適用例: : Mono (DegenerateHornInput.boundary i d K) |
| check_relative_lift_choices.lean | 落ちる | 74 | 74 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 74 宣言の推移的公理依存。型指定: CoherentLiftRelative.postChoiceSpace_extension。適用例: {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P) (p : P ⟶ SSet.stdSimplex.{v}.… |
| check_replacement_mapping_descent.lean | 通る | 128 | 128 | 21 | 0 | 0 | 所有モジュール／名前空間から選ぶ 128 宣言の推移的公理依存。型指定: FibrantReplacementObject.toIdentityPresentation。適用例: (X : C) : (FibrantReplacementObject.ofObject X).base = X |
| check_resolution_action_operators.lean | 落ちる | 43 | 43 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。型指定: ResolutionArrowActionTransport.raw_transport |
| check_resolution_arrow_cylinder_boundary.lean | 落ちる | 59 | 59 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 59 宣言の推移的公理依存。型指定: glue_zero |
| check_resolution_arrow_diagram.lean | 落ちる | 70 | 70 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 70 宣言の推移的公理依存。型指定: ArrowContext.parameters。適用例: (s : NerveSimplexEndpoint.Index E) : (NerveCoherentReindex.reindex H F a).app s = a.app ((NerveCoherentR… |
| check_resolution_arrow_endpoints.lean | 落ちる | 49 | 49 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 49 宣言の推移的公理依存。型指定: NerveBiparameterMaps.reindex |
| check_resolution_arrow_family_fit.lean | 落ちる | 38 | 38 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: NerveMovingFamilyFit.extend_evaluate。適用例: : extendFamilies C hcof d ≫ NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lift… |
| check_resolution_arrow_tuple_coherence.lean | 落ちる | 45 | 45 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 45 宣言の推移的公理依存。型指定: NerveRelativeNaturalBoundary.extend_evaluate。適用例: (q : ResolutionArrowDiagram.Index C) (k : StrictLift C q) (n : ℕ) : VertexTuples.si… |
| check_resolution_bar_cone_diagram.lean | 通る | 42 | 42 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 42 宣言の推移的公理依存。型指定: ResolutionBarConeDiagram.left |
| check_resolution_bar_evaluation.lean | 落ちる | 66 | 66 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 66 宣言の推移的公理依存。型指定: NerveFirstChoice.extend_restrict |
| check_resolution_bar_frame_squares.lean | 通る | 51 | 51 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 51 宣言の推移的公理依存。型指定: FrameLiftSpace.outerMap_diagram |
| check_resolution_bar_row_homotopy.lean | 落ちる | 34 | 34 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 34 宣言の推移的公理依存。型指定: BarConstruction.commaSectionHomotopy |
| check_resolution_bar_simplex_cone.lean | 通る | 44 | 44 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 44 宣言の推移的公理依存。型指定: ResolutionLiftRows.map |
| check_resolution_frame_rows.lean | 通る | 96 | 96 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 96 宣言の推移的公理依存。型指定: ResolutionFrameRows.augmentation_base。適用例: (X : ResolutionObject C) (n : SimplexCategory) : (ResolutionFrameRows.row X n).base = X.ba… |
| check_resolution_hom.lean | 落ちる | 10 | 10 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: chosenResolutionHom。適用例: (X : Cᵒᵖ) (Y : C) (n : SimplexCategoryᵒᵖ) : (((chosenResolutionHom cof fib).obj X).obj Y).… |
| check_resolution_hom_comparison.lean | 通る | 83 | 83 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 83 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ChosenComparison.left |
| check_resolution_hom_kan.lean | 落ちる | 18 | 18 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialResolution_hom_kanComplex |
| check_resolution_hom_pi_zero.lean | 落ちる | 66 | 66 | 4 | 2 | 0 | 所有モジュール／名前空間から選ぶ 66 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: resolutionPiZeroLocalizationEquiv |
| check_resolution_hom_source.lean | 落ちる | 42 | 42 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 42 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialHomMap_weakEquivalence |
| check_resolution_hom_target.lean | 落ちる | 7 | 7 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: cosimplicialHom_trivialFibration。適用例: : SerrePositivity.SimplicialModelInputs.geometricWeakEquivalences.{v} = SerreP… |
| check_resolution_lift_spaces.lean | 通る | 63 | 63 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 63 宣言の推移的公理依存。型指定: ResolutionLiftSpace.projection_trivialFibration。適用例: {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}] (hcof :… |
| check_resolution_mixed_boundary.lean | 落ちる | 38 | 38 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: NerveMovingBoundary.boundary_face |
| check_resolution_mixed_diagonal.lean | 落ちる | 50 | 50 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 50 宣言の推移的公理依存。型指定: coherent_recover |
| check_resolution_mixed_edges.lean | 落ちる | 143 | 143 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 143 宣言の推移的公理依存。型指定: edge_commutes |
| check_resolution_mixed_endpoints.lean | 通る | 79 | 79 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 79 宣言の推移的公理依存。型指定: left_follow |
| check_resolution_mixed_small_action.lean | 落ちる | 37 | 37 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 37 宣言の推移的公理依存。型指定: NerveSmallFamilies.family |
| check_resolution_mixed_triangles.lean | 落ちる | 57 | 57 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。型指定: NerveMovingBoundary.boundary_vertices |
| check_retract_word_presentation.lean | 落ちる | 10 | 10 | 14 | 0 | 1 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: RetractWords.augmentation。適用例: : Category.{max u v w} (RetractWords.Small C M) |
| check_right_resolution_mapping.lean | 通る | 76 | 76 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 76 宣言の推移的公理依存。型指定: DualResolutionTargets.presentation_projection。適用例: : (DualResolutionTargets.framedBase C).Full |
| check_selected_interval_diagram.lean | 落ちる | 87 | 87 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 87 宣言の推移的公理依存。型指定: UniverseLift.lowerSimplexTensor_simplexTensorMap |
| check_selected_mixed_comparison.lean | 落ちる | 108 | 108 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 108 宣言の推移的公理依存。型指定: SelectedTriangle.Boundary.compatible。適用例: : SSet.stdSimplex.δ (0 : Fin 3) ≫ CoherentLiftMixedComparison.triangle hcof hfib X Y W V f… |
| check_selected_postcomposition_triangle.lean | 落ちる | 69 | 69 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 69 宣言の推移的公理依存。型指定: CoherentLiftPostComposition.faces_compatible。適用例: : SSet.stdSimplex.δ (0 : Fin 3) ≫ CoherentLiftPostComposition.triangle hcof hfib X … |
| check_selected_precomposition_triangle.lean | 落ちる | 67 | 67 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 67 宣言の推移的公理依存。型指定: CoherentLiftPreComposition.faces_compatible。適用例: : SSet.stdSimplex.δ (0 : Fin 3) ≫ CoherentLiftPreComposition.triangle hcof hfib X Y … |
| check_selected_unit_comparison.lean | 落ちる | 43 | 43 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。型指定: SelectedLoopContraction.degenerate_vertex。適用例: (post : Bool) : SSet.stdSimplex.δ (1 : Fin 2) ≫ CoherentLiftUnitComparison.loop hcof h… |
| check_simplex_index_finite.lean | 通る | 36 | 36 | 13 | 0 | 0 | 所有モジュール／名前空間から選ぶ 36 宣言の推移的公理依存。型指定: Reedy.elementsLatchingIndex_finite。適用例: [Finite (Reedy.MatchingIndex r x.obj)] : Finite (Reedy.MatchingIndex (Reedy.elementsReedy P r… |
| check_simplex_latching_boundary.lean | 通る | 90 | 90 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 90 宣言の推移的公理依存。型指定: Reedy.elementsMatchingEquivalence |
| check_simplex_nerve_equivalence.lean | 落ちる | 27 | 27 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 27 宣言の推移的公理依存。型指定: CellularNaturalComparison.app_isIso |
| check_simplex_nerve_standard.lean | 通る | 43 | 43 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。型指定: isColimitOfPreserves。適用例: (X : SSet.{v}) : SimplexNerve.functor.obj X = nerve X.Elements |
| check_simplex_presentation_equivalence.lean | 落ちる | 12 | 12 | 20 | 0 | 0 | 所有モジュール／名前空間から選ぶ 12 宣言の推移的公理依存。型指定: SimplexPresentation.equivalence。適用例: : toSimplexCategory.Faithful |
| check_simplicial_level.lean | 通る | 22 | 22 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 22 宣言の推移的公理依存。型指定: simplicialLevelModelCategory。適用例: {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) : let |
| check_simplicial_level_tensor.lean | 通る | 16 | 16 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 16 宣言の推移的公理依存。型指定: SymmetricSpectrum.freePushoutProductIso |
| check_simplicial_map_comparison.lean | 通る | 70 | 70 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 70 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ChosenMapComparison.geometricWeakEquivalences。適用例: (cof : MorphismProperty.FunctorialFactorizationData (cofibration… |
| check_simplicial_model_inputs.lean | 通る | 33 | 33 | 21 | 0 | 0 | 所有モジュール／名前空間から選ぶ 33 宣言の推移的公理依存。型指定: _root_.SerrePositivity.SimplicialModel.boundaryGenerator_domain_presentable |
| check_simplicial_monoidal.lean | 通る | 4 | 4 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 4 宣言の推移的公理依存。型指定: _root_.SerrePositivity.SimplicialModel.simplicial_pushoutProduct_mono |
| check_simplicial_tensor_frame.lean | 落ちる | 33 | 33 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 33 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SerrePositivity.SimplicialHomotopy.stdSimplex_map_weakEquivalence |
| check_simplicial_tensor_hom.lean | 落ちる | 14 | 14 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 14 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: tensorHomBifunctorIso。適用例: (Q R : C ⥤ C) (X : Cᵒᵖ) (Y : C) : ((resolutionHom (Q ⋙ tensorCosimplicialFamily S) R).ob… |
| check_simplicial_universe_lift.lean | 落ちる | 20 | 20 | 11 | 2 | 0 | 所有モジュール／名前空間から選ぶ 20 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: boundaryArrowIso。適用例: : PreservesColimitsOfSize.{v, v} SSet.uliftFunctor.{w, v} |
| check_skeletal_cell_coherence.lean | 落ちる | 49 | 49 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 49 宣言の推移的公理依存。型指定: SkeletalCellGluing.glue_cell。適用例: : Nonempty (SkeletalCellGluing.Rule (Q := CoherentLiftRelative.obj X Y f) j) |
| check_small_diagram_quotient.lean | 落ちる | 19 | 19 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 19 宣言の推移的公理依存。型指定: SmallDiagramQuotient.projection |
| check_small_dominated_subcomplex.lean | 落ちる | 40 | 40 | 8 | 0 | 0 | 所有モジュール／名前空間から選ぶ 40 宣言の推移的公理依存。型指定: SmallDominatedSubcomplex.small |
| check_small_hom_locality.lean | 落ちる | 31 | 31 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SmallHomComparison.sourceArrowIso |
| check_small_subdiagram_obstruction.lean | 落ちる | 32 | 32 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 32 宣言の推移的公理依存。型指定: AnodyneNonempty.nonempty_iff_of_localized_isIso。適用例: (I : Type u) : LocallySmall.{0} (Index I) |
| check_smith_completeness.lean | 通る | 3 | 3 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 3 宣言の推移的公理依存。型指定: locallyPresentable_hasLimits。適用例: {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] : HasFiniteLimits C |
| check_smith_coproduct_closure.lean | 通る | 35 | 35 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 35 宣言の推移的公理依存。型指定: sigma_mem。適用例: {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C] (I J W : MorphismProperty C) [J.IsSmall.{w}] [W.IsStableUnd… |
| check_smith_existence.lean | 落ちる | 16 | 16 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 16 宣言の推移的公理依存。型指定: smithGenerators_factor。適用例: : letI : CategoryWithCofibrations C |
| check_smith_generators.lean | 通る | 40 | 40 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 40 宣言の推移的公理依存。適用例: : ∃ J : MorphismProperty C, J.IsSmall.{w} ∧ J.HasSmallObjectArgument.{w} ∧ J ≤ I.rlp.llp ⊓ W ∧ ∀ (i f : Arrow C), I i.hom → W f.hom →… |
| check_smith_recognition.lean | 通る | 10 | 10 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: generatedLeft_eq_of_square_factor。適用例: : ∃ J : MorphismProperty C, J.IsSmall.{w} ∧ I.rlp = J.rlp ⊓ W |
| check_smith_smallness.lean | 通る | 5 | 5 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 5 宣言の推移的公理依存。型指定: exists_common_presentability。適用例: [IsLocallyPresentable.{w} C] (I : MorphismProperty C) [I.IsSmall.{w}] : I.rlp.llp.HasFunctorialFacto… |
| check_smith_solution_set.lean | 通る | 18 | 18 | 10 | 0 | 0 | 所有モジュール／名前空間から選ぶ 18 宣言の推移的公理依存。型指定: solutionSetCondition。適用例: {ι : Type t} [Small.{w} ι] (a : ι → Arrow C) : (solutionTargets W a).IsSmall.{w} |
| check_source_contraction.lean | 落ちる | 81 | 81 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 81 宣言の推移的公理依存。型指定: ExtraDegeneracyContraction.contraction |
| check_span_hocolim.lean | 通る | 12 | 12 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 12 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ProjectiveReindexing.llp_map。適用例: {P D : WalkingSpan ⥤ C} (i : P ⟶ D) (hP : IsInitial P) (hi : ((trivialFibrations … |
| check_spectra_level_left_proper.lean | 落ちる | 15 | 15 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 15 宣言の推移的公理依存。適用例: {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOf… |
| check_spectra_presentability.lean | 通る | 7 | 7 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。型指定: Smith.ConservativeAdjunction.isLocallyPresentable |
| check_spectra_stage2.lean | 通る | 0 | 0 | 25 | 0 | 0 | 型指定: pointwiseTensorCotensorAdjunction |
| check_spectrum_derived_tensor_inverse.lean | 落ちる | 70 | 70 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 70 宣言の推移的公理依存。適用例: {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOf… |
| check_spectrum_level_classes.lean | 落ちる | 6 | 6 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 6 宣言の推移的公理依存。型指定: levelGenerators_rlp |
| check_spectrum_level_generators.lean | 落ちる | 39 | 39 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 39 宣言の推移的公理依存。型指定: levelModelCategoryOfGenerators |
| check_spectrum_level_model.lean | 落ちる | 25 | 25 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 25 宣言の推移的公理依存。型指定: levelModelCategory |
| check_spectrum_omega_local_objects.lean | 落ちる | 11 | 11 | 1 | 0 | 0 | 所有モジュール／名前空間から選ぶ 11 宣言の推移的公理依存。適用例: {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOf… |
| check_spectrum_stabilization_maps.lean | 落ちる | 38 | 38 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 38 宣言の推移的公理依存。型指定: localizingMap。適用例: {ι : Type t} [Small.{w} ι] (A : ι → C) : (localizingMaps K A).IsSmall.{w} |
| check_spectrum_stable_enriched.lean | 落ちる | 13 | 13 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 13 宣言の推移的公理依存。型指定: m |
| check_spectrum_stable_model.lean | 落ちる | 31 | 31 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: p.localization.model。適用例: {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfS… |
| check_spectrum_suspension_geometry.lean | 落ちる | 97 | 97 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 97 宣言の推移的公理依存。型指定: PointedObject.cofiber_isPushout。適用例: [ModelCategory SSet.{u}] (K : PointedSimplicialSet.{u}) [original : ModelCategory (GeneralSymmet… |
| check_spectrum_tensor_inverse.lean | 通る | 7 | 7 | 2 | 0 | 0 | 所有モジュール／名前空間から選ぶ 7 宣言の推移的公理依存。型指定: p.localizingMap_isWeakEquivalence。適用例: [IsCofibrant (𝟙_ C)] {H : Type uH} [Category.{vH} H] (Q : GeneralSymmetricSpectrum C K ⥤ H) [Q.… |
| check_strict_value_descent_counterexample.lean | 通る | 45 | 45 | 17 | 0 | 0 | 所有モジュール／名前空間から選ぶ 45 宣言の推移的公理依存。型指定: point_kanComplex。適用例: : projection.{v}.Full |
| check_strong_retract_transfer.lean | 通る | 66 | 66 | 6 | 0 | 0 | 所有モジュール／名前空間から選ぶ 66 宣言の推移的公理依存。型指定: MonoRightLiftingRelativeHomotopy.exists_strong_contraction |
| check_tensor_gluing.lean | 通る | 43 | 43 | 8 | 2 | 0 | 所有モジュール／名前空間から選ぶ 43 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SubcomplexTensor.functor。適用例: {n : SimplexCategory} (S T : (SSet.stdSimplex.{v}.obj n).Subcomplex) : IsPushout (Sub… |
| check_universe_lift_anodyne.lean | 落ちる | 5 | 5 | 5 | 0 | 0 | 所有モジュール／名前空間から選ぶ 5 宣言の推移的公理依存。型指定: SerrePositivity.ModelGeneration.generatedLeft_map。適用例: {D : Type u} [Category.{v'} D] {B : Type u'} [Category.{t} B] (p : D ⥤ B) (F : … |
| check_universe_lift_anodyne_reflection.lean | 落ちる | 62 | 62 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 62 宣言の推移的公理依存。型指定: KanHomotopyExtension.exists_homotopy |
| check_universe_lift_parameter_hom.lean | 落ちる | 31 | 31 | 9 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: SimplexParameterHom.nativeIso |
| check_weak_equivalence_filtered_colimits.lean | 通る | 10 | 10 | 3 | 0 | 0 | 所有モジュール／名前空間から選ぶ 10 宣言の推移的公理依存。型指定: AccessibleLiftingClosure.rlp_of_isColimit |
| check_weak_equivalences_accessible.lean | 通る | 21 | 21 | 4 | 0 | 0 | 所有モジュール／名前空間から選ぶ 21 宣言の推移的公理依存。型指定: exists_accessible_rightClass_inverseImage。適用例: : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∃ d : AccessibleModelFactorizations C κ… |
| check_weighted_frame_limit.lean | 通る | 79 | 79 | 5 | 2 | 0 | 所有モジュール／名前空間から選ぶ 79 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: FrameWeightRealization.adjunction |
| check_weighted_source_comparison.lean | 通る | 54 | 54 | 8 | 2 | 0 | 所有モジュール／名前空間から選ぶ 54 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: ConstantWeightRealization.iso |
| check_weighted_source_naturality.lean | 通る | 49 | 49 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 49 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: WeightedSourceComparison.comparisonFamily |
| check_weighted_source_weak_equivalence.lean | 通る | 31 | 31 | 3 | 2 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: SmallHomYonedaWeight.iso |
| check_word_chain_transfer.lean | 落ちる | 0 | 0 | 14 | 0 | 0 | 型指定: WordRetractChainFamily.interior_identity |
| check_word_presentation_action.lean | 落ちる | 8 | 8 | 7 | 0 | 0 | 所有モジュール／名前空間から選ぶ 8 宣言の推移的公理依存。型指定: small_naturality |
| check_word_resolution_diagram.lean | 落ちる | 19 | 19 | 14 | 0 | 0 | 所有モジュール／名前空間から選ぶ 19 宣言の推移的公理依存。型指定: RetractWords.map_augmentation |
| check_word_retraction_action.lean | 落ちる | 52 | 52 | 12 | 0 | 0 | 所有モジュール／名前空間から選ぶ 52 宣言の推移的公理依存。型指定: action |
| check_word_rows_diagonal.lean | 落ちる | 31 | 31 | 11 | 0 | 0 | 所有モジュール／名前空間から選ぶ 31 宣言の推移的公理依存。型指定: AmbientWords.map_id |
| check_word_segment.lean | 落ちる | 0 | 0 | 17 | 0 | 1 | 型指定: Word |
| check_yoneda_homotopy_weight.lean | 通る | 57 | 57 | 6 | 2 | 0 | 所有モジュール／名前空間から選ぶ 57 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出。型指定: YonedaWeights.colimitIso |
| refactor/check_cleanup_c2.lean | 落ちる | 24 | 24 | 0 | 2 | 7 | 所有モジュール／名前空間から選ぶ 24 宣言の推移的公理依存。監査モジュールの照合・実行漏れ検出 |
| refactor/check_deprecated_aliases.lean | 通る | 0 | 0 | 0 | 1 | 0 | 入力で指定した互換定義の定数本体・宇宙・型・公理を比較。公理辺の採取モードもある |
| refactor/test_dag_hash.lean | 通る | 0 | 0 | 0 | 5 | 0 | 共有あり／なしの Expr のハッシュ一致、異なる子での不一致、DAG 展開数を検証 |
| refactor/test_proof_irrelevant_hash.lean | 通る | 0 | 0 | 2 | 5 | 0 | 定理名・宇宙引数・生成参照・再帰補助のハッシュを構成例で照合。。適用例: theorem eqA (α : Sort u) (x : α) : x = x |
| refactor/tests/deprecated_alias.lean | 通る | 0 | 0 | 13 | 4 | 0 | 型指定: b.val。適用例: : IFDeprecatedAliasTests.Old.Box Nat |

</details>

## 対応表との照合

対応表にある宣言欄を CSV／TSV 123 件、公開用の地図データ 5 件、旧カーネル対応表から集めた。
所有元付きで照合できたのは 9,065 宣言。CSV の `coverage_names` は各スクリプトの対象集合との共通部分の件数。
現行本体に解決できなかった 1,777 種の表記には外部宣言、旧名、曖昧な短名を含む。
宣言名を一意に読めない注記や式は別途証拠に残した。

## root の外のビルド範囲

root 外は 4,387 モジュール。manifest の監査が届くのは 4,211 本で、そのうち一つの監査にしか届かないのは 2,794 本。
非掲載だけが届くのは 0 本。どの現行 Lean スクリプトの固定 import からも届かないものは 176 本。
直接 import とリテラルの runtime import から閉包を取った。CLI の引数で決まる import は固定の依存に加えていない。
本体の集計は Archive と外部パッケージを除く。表の `transitive_imports` は外部も含め、`project_closure` は本体だけを数える。
行を折り返した import は保存索引とソース解析で照合した。調査では閉包の外も別途ビルドし、宣言の母集団をそろえた。

| ディレクトリ | manifest 経由 | うち単独 | 非掲載のみ | 全調査外 |
| --- | --- | --- | --- | --- |
| SerrePositivity/Asymptotic | 2 | 2 | 0 | 0 |
| SerrePositivity/BhattScholze | 1 | 1 | 0 | 0 |
| SerrePositivity/CategoryTheory | 20 | 0 | 0 | 0 |
| SerrePositivity/DifferentialGraded | 309 | 304 | 0 | 0 |
| SerrePositivity/HomotopicalAlgebra | 704 | 418 | 0 | 106 |
| SerrePositivity/InfinityCategories | 1024 | 403 | 0 | 10 |
| SerrePositivity/KST | 1914 | 1594 | 0 | 60 |
| SerrePositivity/Spectra | 236 | 71 | 0 | 0 |
| SerrePositivity/Util | 1 | 1 | 0 | 0 |
| 合計 | 4211 | 2794 | 0 | 176 |

## 扱いの案と取り込みの時間

| 案 | manifest 掲載 | 非掲載 |
| --- | --- | --- |
| そのまま | 89 本 / 130,705 行 / 1.28 時間 | 147 本 / 11,876 行 / 20.7 分 |
| まとめる | 14 本 / 2,270 行 / 5.9 分 | 0 本 / 0 行 / 0.0 分 |
| 本体に移す | 0 本 / 0 行 / 0.0 分 | 5 本 / 427 行 / 0.6 分 |
| 消す | 5 本 / 42,927 行 / 3.4 分 | 0 本 / 0 行 / 0.0 分 |
| 直す | 0 本 / 0 行 / 0.0 分 | 163 本 / 14,494 行 / 25.7 分 |

| 仮定 | 本数 | 延べ実行時間 | 全体直列・その他最大 6 枠 | 同左＋別段の sorry 閉包 |
| --- | --- | --- | --- | --- |
| 現行 manifest | 108 | 1.44 時間 | 21.1 分 | 24.1 分 |
| 消す／まとめる案だけを適用 | 89 | 1.28 時間 | 19.5 分 | 22.5 分 |

全体読み込みを直列にし、残りを六枠で割り付けた概算。実際の root は 18.3 秒、対象ビルドはこの作業木で延べ 38.3 秒。
候補を一度に適用した場合に失われる root 外の固定 import は 25 モジュール。単独削除では固有でない場合も含む。この差は別のビルド対象で補う。
このモデルには中規模同士の追加の重なり制限、鍵待ち、全体機構の開発、修正後の未計測時間、追加対象の再ビルドを含めていない。
印字を消す候補でも、固有の import や対応表が必要とする名指しは代わりの検査を確認してから扱う。

## 三つの仕組みに残る作業

1. 全モジュールのビルド対象は追跡する本体 .lean の一覧から生成し、Archive と外部パッケージを区別する。
   manifest が唯一の経路になっているモジュールをこの一覧で覆い、root でしか試験しないケースと区別する。
2. 宣言の公理・sorry はモジュールごとの保存成果物から所有元付きのリストを作り、全体を import するプロセスを重ねない。
   許可公理、文献入力の許可、直接の禁止依存を条件として明示し、領域監査の厳格な条件を保てるか差分で確認する。
3. 対応表の名指しは現在の所有元とカーネル名に解決し、型構造を基準コミットに結び付けて保存する。
   数だけの増減、誤った所有元、存在する別宣言へのすり替わりを分けて検出する。

## 判断を保留したもの

表の各行に扱いの案と根拠を記録した。

基準 root の計測からこの集計まで約 3.15 時間。ロック待ちを含む。
証拠の場所は `/Users/sugakubunka/serre-evidence/ar-w1/eac7d1e57`。ソース位置、展開した宣言集合、実行結果と環境再試行のログを保存した。
段 1 はこの表と報告で停止。

## AR-W1 段3　全モジュールの採取と並行検証

基準 main は `cc25cf900`。旧監査・manifest・本体は基準のまま検証した。再計算の次の設計は [再計算監査の設計案](recompute-audit-design.md)。

### 母集団と成果物の鮮度

追跡対象は Archive を除く本体34,250モジュール。Archive 1,802本、旧 `scripts/` 424本、blueprint 175本、研究・計画・証拠の Lean 103本は別集計。Lake の通常の build コマンドに全対象を渡した。長い引数を避けるため、新しい入口は対象一覧をファイルから読んで同じ CLI を呼び出す。

読む前に Lake の `--no-build --rehash --no-cache` で入力 trace を照合し、対象ごとの `.trace` にある出力ハッシュを同じ Lake の実ハッシュ計算で確かめた。読む前後のソース、trace、成果物のファイル印も照合した。小さな独立プロジェクトの古いソース・不正な成果物ハッシュを用いた負例は後掲。前提は、Lake の依存記録と、同じ版の Lean・Mathlib・固定パッケージに従ってビルドした成果物。出力のハッシュは改ざんに対する署名ではない。

| 集合 | モジュール | 差分 |
| --- | --- | --- |
| 追跡 | 34,250 | 0 |
| Lake で確認済み | 34,250 | 0 |
| 採取 | 34,250 | 0 |
| 判定 | 34,250 | 0 |

### G2 と Lean の公理

表のキーは所有元とカーネル名。型と値を別々に指紋化し、型の辺・値の辺・コンストラクタ辺を別に保存した。公開性、private、内部名、位置の有無、保存された instance・実装属性、unsafe、partial を含む。位置のない生成宣言も行として保持した。

**G2 合格**。本体 360,168 宣言。未判定 0、許可外の公理に依存する宣言 0、直接 sorry 4 件、推移的な sorry 依存（直接分も含む）164 件。

由来の補助索引は source-command 163,044、kernel-generated 142,034、unclassified 55,090。由来の保留行にも公理判定を行った。

種類は thm 251,569、def 105,695、rec 911、ctor 1,063、inductive 911、opaque 19。

公理の取得経路は import 65,008、stored 295,160。

属性・位置などは 公開側 295,160、private 名 66,410、内部名 182,046、位置あり 175,258、値あり 357,283、instance 登録あり 5,386、unsafe 0、partial 406、extern 0、implemented_by 0。

| 許可入力 | 直接 | 依存する宣言（直接を含む） | 主定理へ到達 |
| --- | --- | --- | --- |
| `SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | 1 | 131 | 有 |
| `SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillen_model_exists` | 1 | 18 | 無 |
| `SerrePositivity.Section4.supportedRankK0_descent` | 1 | 17 | 有 |
| `SerrePositivity.theorem_3_1_K0` | 1 | 16 | 有 |

依存する宣言の領域別件数（領域や入力によって重複する）。

| 領域 | 宣言数 |
| --- | --- |
| SerrePositivity.BhattScholze.Inputs | 1 |
| SerrePositivity.BhattScholze.Perfectoidization | 39 |
| SerrePositivity.CLMST.Algebra | 7 |
| SerrePositivity.CLMST.KoszulAnnihilation | 27 |
| SerrePositivity.CLMST.ParameterPowerLength | 9 |
| SerrePositivity.CLMST.ParameterQuotientLength | 18 |
| SerrePositivity.CLMST.PerfectoidizationIsogeny | 19 |
| SerrePositivity.InfinityCategories.Project | 18 |
| SerrePositivity.Inputs.Descent | 1 |
| SerrePositivity.Paper.Section2 | 3 |
| SerrePositivity.Paper.Section3 | 2 |
| SerrePositivity.Paper.Section4 | 3 |
| SerrePositivity.Paper.Section5 | 15 |
| SerrePositivity.Paper.Statement | 2 |

### 旧い領域監査との照合

旧監査 76 本。所有元付きの一致は宣言の和集合で 261,830 件、延べ 327,755 判定。選択の欠落 0、追加 0、許可判定の差 0。

旧の判定根拠は段1の実行ログと、選択式・所有元索引。各実行のソース SHA256 と対象の Lean ソース・依存の同一性を確認し、同じ入力として照合した。新しい表から対象と許可集合を再構成した。差の個別一覧は `legacy/region-differences.json`。

表へ移した条件は、名指しの厳格な sorry、領域の型禁止辺、期待するモジュールの訪問、公理宣言の種類、直接 sorry の許可ファイル、主定理の旧入口と S-1 の import 境界、K-cofinality の証明経路。この実行の規則数は 119、違反 0。内訳は direct_sorry_file_rules 5、visited_module_rules 61、strict_sorry_keys 5,107、kind_rules 2、type_suffix_rules 2、type_predicates 22。

公開性と所有元の個別条件は表の項目と規則の機能を用意した。指定型への適用、展開後の整合・実際の instance、F2 の互換属性、引用登録、旧監査固有の残りの構造条件とソース字面の直接 sorry 探索は旧検査を維持する。

段1の名指し5,133命令のうち8件は同じスクリプト内で同じキーを再度検査する。F4〜F7 のスクリプト局所例に対する18命令は別の試験に残した。

### 全宣言の再計算と版更新の自己試験

鮮度を再確認した後に、環境を分けて Lean の `collectAxioms` を呼んだ。360,168/360,168 宣言、34,250 モジュール、欠落 0、差 0。結果は **合格**。

Lean の通常の import で使える定数は、公開定数の保存拡張を Lean 自身が使う。同名で別の所有元が隠れたときは、そのレコードの型と値を一時の別名として核で検査し直し、その公理を採った。

再計算の経路別内訳は import 358,655、owner-record 1,513。

import は 7 塊。宣言のない import 専用 236 モジュールは、鮮度が通ったソース全文から宣言コマンドがないことを別に確かめた。ここに属する root の巨大な再読み込みを省いた。

自己試験は試験用 28 宣言（保存なし 1）と規則の負例 10 件。異なる公理を持つ同名宣言の二つの所有元、ソースの変更後に古い成果物を読む試み、出力ハッシュが不正な成果物も検証した。

Mathlib を import する Citation の 71 宣言も、衛生的マクロ名を含む未保存分 10 件まで別に照合した。

| 塊 | 対象モジュール | 外部を含む import 閉包 | Lean 秒 | 最大 RSS (GiB) |
| --- | --- | --- | --- | --- |
| 0 | 17,013 | 23,000 | 164.4 | 6.74 |
| 1 | 2,939 | 18,500 | 82.8 | 5.57 |
| 2 | 3,124 | 18,500 | 82.8 | 5.74 |
| 3 | 757 | 18,500 | 82.0 | 5.44 |
| 4 | 1,800 | 18,500 | 84.7 | 5.57 |
| 5 | 2,698 | 18,500 | 76.1 | 5.54 |
| 6 | 5,683 | 17,980 | 94.2 | 6.20 |

### 計測

| 測定 | 鍵待ち（秒） | Lake（秒） | 成果物ハッシュ（秒） | 直接採取（秒） | Lean 取得（秒） | 実行全経過（秒） |
| --- | --- | --- | --- | --- | --- | --- |
| 全体の対象 build | 1.0 | 21.9 | 0.0 | 0.0 | 0.0 | 35.6 |
| 全体の直接採取（再開前） | 0.5 | 24.3 | 38.3 | 95.8 | 0.0 | 401.5 |
| 全体の公理補完（先の4塊） | 1.0 | 21.6 | 37.5 | 0.0 | 698.1 | 846.0 |
| 全体の公理補完（残り） | 0.8 | 23.4 | 37.6 | 0.0 | 236.9 | 424.5 |
| 全体の再計算 | 2.2 | 23.0 | 37.2 | 0.0 | 667.0 | 881.1 |
| 差分（1 モジュール） | 0.2 | 21.6 | 43.8 | 0.036 | 5.6 | 168.3 |
| 手元の部分（Citation） | 0.8 | 8.9 | 1.4 | 0.034 | 6.2 | 51.2 |

G2 判定は全体 8.8秒、旧76本との照合は 14.8秒。全体の直接採取は95.8秒、未保存公理の補完はLeanの実行だけで935.0秒。全経過には道具のコンパイル、I/O、待機、集計が入る。再計算の全経過は最後の再開からで、Lean の秒数は完了した全塊の合計。差分は Lean ファイルを変えず、前回テーブルから1モジュールの行を抜いて再採取を誘発した。実際に更新した対象は 1 本。概念の木は旧入口で HTML まで生成した。畳み込み後の循環で旧割り当て器が止まったため、互換ビューに限って 155 本の後方辺を外した。元の全依存、折り畳み結果、変更した辺の一覧を保全した。

資源限界の診断を調べた。最初の補完は採取を終えた後、起動前の vnode 余裕が大きな塊の見積もりを下回った。未起動の試行を保全し、より小さな塊と中断時のチェックポイントを入れた。

`Too many open files in system` は段3の試行で 0 回。同診断による再試行は0回。最初の補完ではマクロ生成名の再パースにより一部の名前を照合できなかった。文字列をそのまま照合するように直し、保存公理だけを持つ直接採取済みのチェックポイントを鮮度の再検査後に再利用した。再計算の最初の大きな塊の一つでは既存成果物の探索に失敗した。現物3部とファイル印を確認し、完了済みの塊を保全して切り直した。

ログ、対象一覧、表、個別比較は `~/serre-evidence/ar-w1/cc25cf900-stage3/`。手順は [audit2 の説明](../../../scripts/audit2/README.md)。

記録監査の入力判定を main `0f85ac6fe` の取り込み後に修正した。別レーンのビルドがハードリンクを張り替えると、監査側で内容が同じ `.olean` の ctime が変わり、旧版は `preflight input changed during audit` で止まった。ソース・trace・成果物の判定を、読み直したバイト数と SHA-256 に変更し、既存の Lake の鮮度・成果物ハッシュ検査も維持した。回帰試験では、別の一時 Git 作業木で実際に Lake を走らせ、リンクが外れて監査側の ctime が変わった後、ビルドが続いている間に採取と再照合を実行した。旧判定で誤停止を再現し、修正版は通った。サイズと mtime を保って変更したソース・trace・成果物はすべて拒否した。bulk 鍵で自己試験と `SerrePositivity.Util.Citation` の部分記録監査を実行し、71宣言で未判定0・G2合格。ファイル数上限の診断・再試行は0件。実行記録は `~/serre-evidence/ar-w1/0f85ac6fe-hardlink-stamps/`。

## AR-W1 段4　文献対応表とブループリント

基準は main `23cbebdfe`。2026-11-20 の初期基準として、この版の Lean の主張を照合済みのものとして受け入れる。成果物の採取は11-21 JST。過去の照合時点の主張は未復元。12文献に `baseline.csv` を置き、項目番号、対応表の位置、所有モジュールとカーネル名、型と意味の指紋、状態、部分対応の種別、理由、版、基準コミットを記録した。過去の照合者や出典の版が表にないときは、その旨を記録した。

### 解決と基準照合

本体34,049モジュールを全数ビルドして記録監査し、359,344宣言を採った。固定 Mathlib 8,602モジュールの成果物からも宣言を採った。対応表の現行11,052行を読み、宣言欄の各参照を数えた。宣言欄が空でリンクを要求する1行も未解決に含む。レビュー済みの項目はレビュー表の行を使い、K は分冊の map、本論文は外部引用の表も読む。

| 文献 | 本体で一意 | 複数 | 見つからない | 固定 Mathlib | 読めない | 短名に候補あり |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| BM18 | 37 | 0 | 2 | 3 | 0 | 2 |
| BS | 308 | 0 | 45 | 0 | 0 | 1 |
| BS17 | 18 | 0 | 0 | 0 | 0 | 0 |
| CLMST | 38 | 0 | 0 | 1 | 0 | 0 |
| DAG13 | 5 | 1 | 2 | 14 | 0 | 3 |
| HA | 540 | 0 | 33 | 407 | 0 | 33 |
| HTT | 869 | 1 | 17 | 231 | 0 | 18 |
| K | 338 | 6 | 196 | 1 | 3 | 179 |
| Kerodon | 2,955 | 7 | 48 | 1,003 | 0 | 54 |
| NS | 7 | 0 | 0 | 0 | 0 | 0 |
| 本論文とその外部引用 | 139 | 0 | 0 | 3 | 0 | 0 |
| Rydh | 23 | 0 | 1 | 4 | 0 | 1 |
| **計** | **5,277** | **15** | **344** | **1,667** | **3** | **291** |

右端の短名は未解決の内数。ルート直下の名前も、`_root_.` が明記されるまで候補として扱う。完全名の衝突、所有元の食い違い、短い名前の候補は自動採用しない。基準と取り直した値の比較は合格した。既存未解決362件、保存位置との差2,018件、消失・指紋変化・新規未解決0件。位置には `.ilean` の宣言名の選択範囲を使い、Mathlib は固定 checkout への相対パスに統一する。段4では対応表本体の位置も書き換えず、更新候補として出力した。

型の指紋は Lean の核の式を対象にする。意味の指紋は主張の型から本体の定義と opaque の型・値、帰納型と構成子の型をたどり、定数名と構造指紋を合わせる。定理の証明で止める。依存の辺に所有元の情報がない場合に本体に同名の候補が複数あれば全てを含める。固定 Mathlib の版を境界とし、版を上げた場合は変更を列挙して新しい基準で承認する。構造の差を検出する指紋なので、同じ意味かどうかは再照合で判断する。

### 生成の前後

旧生成器の再実行は追跡済みの4,925カードについて配置とリンク配列が一致した。ファイル本文の差は Kerodon §6.2 の import 1本の並び順だけだった。新生成器は、既存未解決のうち生成対象の88参照（BM18 2、HA 19、HTT 18、Kerodon 48、Rydh 1）で書き出し前に停止した。以下は Git 外の診断用出力を旧生成器の再実行と比較した数。診断用出力で参照を省いた箇所は一覧に残る。

| 文献 | 差の出たカード | 旧生成器で落ちていたリンク | 厳格な解決で外れるリンク |
| --- | ---: | ---: | ---: |
| BM18 | 1 | 3 | 0 |
| CLMST | 1 | 1 | 0 |
| HA | 23 | 10 | 19 |
| HTT | 27 | 16 | 15 |
| Kerodon | 100 | 74 | 47 |
| 本論文とその外部引用 | 4 | 5 | 0 |
| Rydh | 6 | 11 | 0 |
| **計** | **162** | **126** | **87** |

カード4,925件と配置は一致。リンクのあるカードは2,363→2,365件、個々のリンクは4,648→4,687件。126件は現行の表から完全名で解決でき、87件は現行の表を完全名として結べない箇所に対応した。Kerodon 4.3.3.1 では表の短名 `IsLowerSet` を旧生成器が `Topology.IsLowerSet` に結んでいた。現行の索引には同じ末尾を持つ3宣言がある。HTT 7.3.1.8 と Kerodon 10.1.2.28 では短名の旧リンクが外れ、同じ行の別の宣言に完全名のリンクが付いた。残りの生成ファイル差分は import、カードのリンク欄、リンクを表示できないときの宣言名表示とその空行、集計値、来歴コメント。見出し、引用、対応の理由、注釈の内容は同じだった。追跡済みの生成物は、未解決を文献担当が確認するまで現行版を保つ。

生成前は対象の解決と基準の一致を確認し、生成後は独立に作ったカードごとの期待リンク配列と照合する。省略されたカードや配列の途中の一つだけが消えた場合も拒否する。各 Lean 生成物に基準コミットと入力の SHA-256 を記す。

### 試験と取り込み案

自己試験は、承認なしの改名・移動、削除、同名の型の変更、型に現れる定義の中身だけの変更、短い名前のすり替わり、同名の所有元の衝突、二つのリンクの片方だけの消失、カードの消失、生成前の未解決を拒否した。承認済みの移動・改名の書き戻し、定理の証明だけの変更、固定 Mathlib の実在名、選択範囲からの行取得は正例で確かめた。

通常の取り込みでは記録監査の後に基準比較を走らせ、主張の指紋変化は不合格とする案。意味だけが変わった場合も既定では停止し、意図した変更をレビュー担当が指定して期限付きで警告扱いにできるようにする。意味は本体の定義をたどり、Mathlib の全体追跡は版更新時の確認に任せる。Verso の運用頻度は以下の実測に基づいて決める。

実行記録は `~/serre-evidence/ar-w1/23cbebdfe-stage4/`。文献・元行・候補の一覧は `all-unresolved.json`、生成差の各カードと解決理由は `compare-blueprint.json`、生成ファイル全差分は `generated.diff`、基準の比較は `baseline-check.json`。重い読込のファイル上限診断と再試行の本数は計測欄に記録する。

### 所要時間

| 処理 | 実測 |
| --- | ---: |
| 全対象ビルド | 40.1秒 |
| 記録監査（同じ指紋のモジュールを再利用、1,719本を再採取） | 360.4秒 |
| 固定 Mathlib の索引（54塊） | 78.2秒 |
| 解決 | 3.32秒 |
| 基準との比較（解決を含む） | 3.45秒 |
| ブループリント生成と出力の照合 | 1.94秒 |

Verso は診断出力を一時作業木に置き、ビルド済みの本体と依存パッケージを使って `lake build SerreBlueprint` を試した。bulk 鍵待ちは12分49.5秒。Lean の読み手を1本にして29分56秒まで測り、生成172モジュールのうち52本のビルドが済んだ。完了した個々の Lean モジュールは1.7〜101秒。30分枠で鍵を返したため、全体の完走時間と HTML 生成時間は未計測。生成器の利用案内を更新した後の出力は、試行時の出力と全172本で来歴コメント以外が同一だった。段4の試行で `Too many open files in system` は0本、同診断によるやり直しは0本。生ログは `verso.log`、今回の計測とモジュールごとの時間は `verso-timing.json`。

この実測から、取り込みごとは基準比較とカード単位のリンク照合までとし、未解決を解消してから生成物を更新する場合や版更新時に、Verso の全体ビルドを別枠で行う案とする。
