module

public import SerrePositivity.LengthAlgebra.PerfectHomologyComparison
public import SerrePositivity.LengthAlgebra.Comparison
public import SerrePositivity.LengthAlgebra.Ordinary
public import SerrePositivity.LengthAlgebra.EulerCompatibility
public import SerrePositivity.PerfectComplex.K0Functoriality
public import SerrePositivity.LengthAlgebra.PerfectMinimalLowerBound

/-! # 単一の長さ付き代数による共通 Euler 理論の実現

有限な長さの商と拡大実数値の商、有限射影支持圏のホモロジー関手、
係数変更、旧 K₀ との比較、任意の Koszul Euler 数による基底公式をまとめる。

実際の Koszul 列と共通の反復錐定理を接続し、有限射影版の消滅・Euler 下界も含む。
極小性から第零ホモロジーの全射を構成し、零次項の階数による具体的下界へ接続した。
有限長さの商と大きな商の有限部分との圏同値、商関手との可換性、長さの保存も含む。
perfect ホモロジーはこの同値に沿って自然に対応し、消滅条件と Euler・K₀ 評価が一致する。
旧 `chiOrdHom`・`chiLamHom_of_finite` も、共通 Euler 評価の引き戻しと一致する。
有限自由／有限射影 K₀ の比較は係数変更と群作用に関して可換し、
局所環上では既存の不変類の降下も有限射影版へ移せる。
-/
