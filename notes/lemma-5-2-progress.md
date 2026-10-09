# Lemma 5.2 の実装状況（2026-10-08）

## 到達点

`Paper/Lemma5_2.lean` を import すると、`CoreData.firstComparison` を使える。
実際の導出は `Core/Lemma52.lean`。帰着後の次元条件・準素条件と
`X.IsPaperData`、以下の標準入力から `X.FirstComparison` を証明した。

- `Inputs.RegularHomologicalAlgebra R`：有界有限自由分解、通常 Tor と係数拡大した
  分解のホモロジーの同定、有限長の交点での Tor の有限長性。
- `Inputs.IntersectionAdditivity R`：両変数での加法性、有限直和の評価。
- `Inputs.FiniteModuleGeometry R`：閉点の交点の有限長性、generic-basis 単射と
  余核の次元低下、正の生成ランクをもつ有限加群・有限整域拡大の次元。
- `Inputs.IntersectionVanishing R`：Roberts–Gillet–Soulé の消滅定理 (5.1)。

これらは `Inputs/IntersectionTheory.lean` の Prop 値 class にした一般的な入力。
インスタンスも axiom も設置していない。どのフィールドも正規化長さ、Galois 群、
ノルム比較や Lemma 5.2 の結論を仮定していない。標準入力の実装は今後の一般論の作業。
**これらを含む全依存関係の形式的証明が完成した、という意味ではない。**

## 証明の接続

1. 標準入力から `E'` の有界有限自由 `R` 分解を取る。
2. `Support/Resolution.lean` で、`D'` に基底変更した複体を閉点に台をもつ
   `IsPerfectSupported` の対象にする。有限長ホモロジーから零ホモトピーへ移す
   一般定理は `Support/NullHomotopy.lean` で証明済み。
3. `Core/NormApplication.lean` で Theorem 2.5 の入力を Lemma 3.5 に渡す。
   `λ` の定義域は `NormalizedLength.restrict` で取り替える。
   必要な極大イデアルの冪の包含は `LocalAlgebra.lean` で証明したので、
   `Inputs/RegularLocalRing.lean` の対応する `sorry` は使わない。
   Koszul 有限性の `v = 0` は、単位元の Koszul 複体が可縮であることから確認。
   3.5 により、ひねった複体の λ の有限性と共役和の等式が得られる。
4. `ResolutionEvaluation.lean` と `TwistEvaluation.lean` で、Tor とホモロジー、
   正規化評価と `c_{σ⁻¹}`、通常評価のひねり不変性を同定する。
   第2変数 `E'` のみを分解し、Tor の対称性は使わない。
5. `OrdinaryEvaluation.lean` で通常評価を `χ^R(D', E')` に同定する。
   剰余体が同じときの長さの比較は、共通ライブラリ
   `CommutativeAlgebra/LengthComparison.lean` の証明を使う。
6. `FiniteExtension.lean` の `chi_finite_extensions` で、generic-basis 単射、
   余核の次元低下、消滅、各変数の加法性を使い `a_D a_E` を取り出す。
7. `Core/FirstComparison.lean` の算術で、逆元による和の取り直しと
   整数値 χ の実数への移送を行い、Lemma 5.2 の結論を得る。

## 編集境界

この作業では Lemma 3.5 とその各側の証明ファイルを編集していない。
並行作業によるファイル再編には、この作業の専用ファイルの import を更新して追従した。
共通の長さ比較との重複は、この作業側を共通ライブラリへ接続して解消した。
import 集約 `SerrePositivity.lean` もこの作業では編集していない。

## 検証と依存関係

`lake build SerrePositivity SerrePositivity.Paper.Lemma5_2` は成功。
今回の新しい証明ファイルと標準入力のインターフェースには `sorry` や axiom 宣言を
追加していない。

`#print axioms`：

- `chi_finite_extensions`、`chiOrd_baseChange_resolution`、
  `isPerfectSupported_baseChange_resolution` は標準公理のみ
  （上記の一般入力は定理の引数）。
- `CoreData.firstComparison` と `normComparison_of_lengthAlgebra` は
  `propext`、`Classical.choice`、`Quot.sound` に加えて `sorryAx` に依存する。
  これは既存の Lemma 3.5 側およびその一般入力の未証明部分に由来する。
  したがって全依存関係を含めた sorry-free 化はまだ残る。
