# K の再開時に確認する参照

AR-W1 段6で備考へ移した8件。対応の状態は表の現行判定を継承する。元行と照合の記録は [段5の一覧](unresolved.csv) にある。

## Archive の6件

- **K 2.12**（状態 `interface`）。`SerrePositivity.KST.Descent.FiniteZariskiCechDescent @ SerrePositivity/Archive/KST/DescentConditional/ZariskiCechLaw.lean:38`。d6c95abcc に Archive の ZariskiCechLaw として入った族の Čech 降下の界面。本体での導来スキーム K の当該界面を改めて確認する案。
- **K 5.1**（状態 `interface`）。`SerrePositivity.KST.Descent.FiniteZariskiCechDescent @ SerrePositivity/Archive/KST/DescentConditional/ZariskiCechLaw.lean:38`。d6c95abcc の Archive の Čech 降下界面。プロ消滅の Zariski 局所性の本体の証明とは区別し、現行界面を再検討する案。
- **K 論文 Lemma 3.2**（状態 `partial`）。`SerrePositivity.KST.Descent.BaseChangeTransfer.cechDescent_of_rank @ SerrePositivity/Archive/KST/DescentConditional/TransferCechDescent.lean:79`。d6c95abcc の Archive の BaseChangeTransfer 補題。正階数 transfer を使った Čech 降下。現在の有理線形の本体補題は同じスペクトルの Čech 降下を述べない。
- **K 論文 Lemma 3.2**（状態 `partial`）。`cechAugmentedPresheafSpace_descent_of_split @ SerrePositivity/Archive/KST/DescentConditional/SplitCechDescent.lean:61`。d6c95abcc の Archive の補題。SplitEpi による空間値増大 Čech 図式の降下で、別の本体の移動先は見つからない。
- **K KST Theorem 2.12**（状態 `interface`）。`FiniteZariskiCechDescent @ SerrePositivity/Archive/KST/DescentConditional/ZariskiCechLaw.lean:38`。d6c95abcc の Archive の有限族 Čech 降下の界面。原文 Theorem 2.12 の本体の供給がないので、界面参照の扱いを承認時に決める。
- **KERODON 9.1.1.20**（状態 `none`）。`SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_isContractibleKan @ SerrePositivity/Archive/InfinityCategories/FilteredExchange/FilteredKanContractibility.lean:69`。4d02ee532 で旧 exchange 経路を Archive へ。旧 Archive の iff と、本体の filtered⇒弱可縮は主張が異なる。none を保持して原典と同型の iff を再確認する案。

## 番号の対応が推定の2件

- **Kuznetsov–Lunts Lemma 4.3・Prop 4.6**（状態 `proved`）。`dgGluingCanonicalNativeSemiorthogonal @ SerrePositivity/InfinityCategories/Project/DerivedCategories/Gluing/CanonicalStableStructure.lean:59`。型は dg gluing の半直交分解を与える。対応表が明記する通り出典は §4.1 のみで、Lemma 4.3 と Prop 4.6 のどちらの主張に対応するかの確認を保留。
- **Kuznetsov–Lunts Lemma 4.3・Prop 4.6**（状態 `proved`）。`semiorthogonalSplitEquivalence @ KST/LocalizingInvariants/SemiorthogonalInvariant.lean:46`。型は半直交 Verdier 列の不変量値の積同値。対応表の番号は推定で、原項目が不変量値の同値を主張する根拠が不足。
