# γ1.5 の旧 API 索引

更新先は [E∞ 代数の計画 §5](stage-i/infinity-lanes/e-infinity-algebras.md#5-記録)。
数学・設計・API の詳細は [InfinityCategories/README.md](../../SerrePositivity/InfinityCategories/README.md)、
正確な型と公理は [監査](../../scripts/audit_dold_kan_comparison.lean) に置く。
実施の経緯と検証はコミットメッセージを参照する。以下は整理前の索引を保存したもの。

### γ1.5：Dold–Kan 豊穣化と dg nerve の比較（進行中）

γ1.5a の設計・符号・原典との照合は `InfinityCategories/README.md` に置く。
比較の向きは `N^hc(C_Δ) → N_dg(C)`。小さい線形 Hom の Kan 性、次数の符号、
閉零射と零単体の同値、標準 chain map 方程式の単体的加群との自然同型、
切断 Hom 複体への Mathlib Γ の適用とその正規化、標準模型の正規化の各項の
具体的な核の共通部分との同定まで実装済み。`standardNormalizationIso x y` は
標準模型の実際の Moore 正規化と `connectiveHomComplex x y` の複体の同型。
`standardDoldKanModuleIso x y : standardModule x y ≅ doldKanHomModule x y`、
`homModuleDoldKanIso x y : homModule x y ≅ doldKanHomModule x y` は単体的加群の自然同型。
`doldKanHomSpaceKan x y : SSet.KanComplex (doldKanHomSpace x y)` は N4 の線形充填から従う。
`awDataBilinear x y z n` は AW 成分族の R 双線形演算。
`awData_unit_left`・`awData_unit_right` は dg 単位の定数単体による両側単位則、
`standardUnitMap x : 𝟙_ SSet.{u} ⟶ standardHomSpace x x` は単体的単位写像。
`awData_assoc h g f : awData h (awData g f) = awData (awData h g) f` は成分族上の結合律。
`awData_pullback α g f` は任意の単調写像 α による引き戻しとの可換性で、退化も含む。
`awData_mem_standard g f` は標準方程式の保存を証明する。
`standardAW (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) :
StandardSimplex R x z n` が追加仮定なしの合成。
γ1.5b は完了。`doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D)`、
`doldKanSimplicialCategory_locallyKan x y : SSet.KanComplex (SimplicialCategory.sHom x y)`、
`doldKanCoherentNerve : SSet.{max u v}` とその quasicategory instance を構成した。
`doldKanSimplicialHomIso` は豊穣 Hom と実際の Mathlib Γ の Hom の自然同型。
通常の圏の恒等射と合成との整合性も証明済み。前提は `[CommRing R] [DGCategory R D]`。
γ1.5c では `cubeEvaluation e φ : GradedHom R x y (-(m : ℤ))` と native Path の
`coherentCubeComponent` を構成し、`cubeFlag_internal_sum_eq_zero` で内部面の相殺を証明した。
`cubeFlag_boundary_sum` は最大旗の全境界を座標1面−座標0面の交代和にする。
`cubeEvaluation_succ_d` は `e : Fin (n+1) ≃ T` と
`φ : Coherent.cube T ⟶ standardHomSpace x y` に対し、
`d (−↑(n+1)) (−↑n) (cubeEvaluation e φ)` が各座標面の評価の差の交代和に等しいと示す。
`cubeEvaluation_zero_closed e φ : differential R (cubeEvaluation e φ) = 0`。
前提は同じく `[CommRing R] [DGCategory R D]`。
`cubeEvaluation_pathFace_zero` は座標0面を一点削除した内部点集合の評価へ移す。
`erasedEnumeration_eq_descending` は降順の向きの保存、`strictAnti_enumeration_card_filter` は係数の点数を与える。
`pathCubeMap_face_one` は座標1面の Path の左右分解、`coherentCube_face_one_apply` は
その豊穣 Hom での像が `standardAW 後半 前半` に等しいことを示す。
前提には `[LinearOrder J]` と実際の豊穣関手 s を用いる。
`standardComponent_nerve_zero_of_not_injOn` は選んだ頂点集合で頂点が重複する成分の消滅、
`cubeEvaluation_restriction_zero` は座標を忘れた正次元の立方体評価の消滅。
`standardTopEval_AW_restriction_zero_of_inversion` は `r<s`、`¬P(e r)`、`P(e s)` の旗を消去し、
`standardTopEval_AW_restriction_eq_term` は `P(e r) ↔ r.val<c.val` の旗の AW を切断点 c の一項にする。
前提は同じ dg 圏と座標立方体からの実際の標準 Hom 写像。
`standardTopEval_AW_cubeSum e f ψ φ` は連結した旗の AW 評価が
`compose R (cubeFlagEvaluation e ψ) (cubeFlagEvaluation f φ)` に等しいと示す。
`standardTopEval_AW_cubeSum_signed_sum` は区間内置換の符号付き二重和が
`compose R (cubeEvaluation e ψ) (cubeEvaluation f φ)` に等しいと示す。次数は `−↑(p+q)`、零次元の因子も含む。
`cubeBlockPermutation_sum` は区間外で零の全置換の和を区間内置換の二重和へ再添字付けする。
`cubeEvaluation_AW_comp e f ψ φ :
cubeEvaluation (cubeSumEnumeration e f) (cubeAWCompositionMap ψ φ) =
compose R (cubeEvaluation e ψ) (cubeEvaluation f φ) _` は全最大旗の評価の合成公式。
同じ前提・次数で零次元も含む。
`pathSplitCoordinateEquiv` は削除後の座標を後半・前半の区間の座標の和へ分け、
`pathSplitEnumeration_eq_descending` は降順の向きの一致を示す。
`coherentCube_split_face` は実際の合成面の Hom 写像と左右の AW 合成写像を同定する。
`cubeEvaluation_coherent_face_one_comp` は `StrictAnti e` の下で、番号付き1面の評価と
左右の標準成分の dg 合成を次数の濃度表示の違いを保った `HEq` で同定する。
前提は実際の豊穣関手と同じ dg 圏・順序。
`coherentCubeComponentAt_d s hab S k l hk hl` は `k=−↑S.card`、`l=k+1` の下で、
指定次数の成分の微分が各内部点での合成項−削除成分の降順符号付き和に等しいと示す。空集合も含む。
`coherentInterior_term_sign` はこの符号を dg nerve の全頂点による符号へ合わせる。
`coherentSimplexData : doldKanCoherentNerve _⦋n⦌ → DGNerve.SimplexData R D n` を構成した。
前提は `[CommRing R] [DGCategory R D]`。既存の `Simplex.equation` への適用と単体的自然性は残る。
公開393宣言の正確な型・前提・公理監査は `scripts/audit_dold_kan_comparison.lean`。残りは
比較写像、低次の一致、写像空間の比較。A3e の `qCatEquivalenceOfFullyFaithfulEssentiallySurjective` は実装済み。
比較写像と各 pinched Hom の実際のホモトピー同値を完成させた後に適用する。
