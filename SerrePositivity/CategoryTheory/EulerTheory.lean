module

public import SerrePositivity.CategoryTheory.EulerComparison
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.CategoryTheory.ConeLengthCancellation

/-! # 長さとホモロジーによる共通理論

付録 B の共通定理への入口。

* `AdditiveLength` / `SerreLength`: 零長さの Serre 部分圏と商、単調性と忠実な長さ。
* `ExactSequenceEuler`: 長完全列の Euler 加法性。具体的な写像錐とも共有する証明。
* `HomologicalEuler`: 有界なホモロジー関手による Euler 評価と K₀ への降下。
* `EulerComparison`: 評価先が異なる二つの Euler 評価の共役和比較。
* `IteratedCone`: 零作用の反復錐の分裂、対象としての消滅、第零次と Euler の下界。
* `ConeLengthCancellation`: 上に有界な係数列の二項変換の一意性。

環、複体列、超極限や論文の個別定理には依存しない。
-/
