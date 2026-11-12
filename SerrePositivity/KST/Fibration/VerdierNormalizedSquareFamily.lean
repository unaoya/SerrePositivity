module
public import SerrePositivity.KST.Fibration.VerdierMovingSharedDiagonal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquarePrismGluing

/-!
概要：正規化した実下側と動く実上側を、同じ全共有対角で貼る。
方針：実上下族を正方形の二三角形表示の押し出しへ渡す。
規約：元の下側への厳密切断を要求せず、正規化族を全体として保持する。
使われ方：K-6 c4 の有限両端照合と元の下側への可逆移送の共通の四角柱。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hdiag : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ N =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ F)

/-- 概要：同じ全共有対角を持つ実上下族の四角柱。
方針：元の二三角形表示と区間の積の押し出しを使う。
規約：上側 F・正規化下側 N を選び直さない。
使われ方：実供給された全上下族の貼り合わせ。 -/
def verdierNormalizedSquareFamily :
    ((Δ[1] ⊗ Δ[1]) ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.desc F N hdiag.symm

/-- 概要：同じ四角柱の上側制限は元の動く全族。
方針：押し出しの第一制限を回収する。
規約：全パラメータでの厳密等式。使われ方：有限上側端点の照合。 -/
theorem verdierNormalizedSquareFamily_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierNormalizedSquareFamily N F hdiag = F :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc _ _ _

/-- 概要：同じ四角柱の下側制限は同じ正規化全族。
方針：押し出しの第二制限を回収する。
規約：元の下側との比較は別に保持する。使われ方：正規化端点の照合。 -/
theorem verdierNormalizedSquareFamily_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierNormalizedSquareFamily N F hdiag = N :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc _ _ _

/-- 概要：同じ四角柱の各時刻の上側は同じ上側族のその時刻。
方針：全族の厳密制限を指定頂点で評価する。
規約：両端を含む全頂点で元の三角形を保持する。
使われ方：指定有限端点二胞体の回収。 -/
theorem verdierNormalizedSquareFamily_vertex_upper (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierNormalizedSquareFamily N F hdiag) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierNormalizedSquareFamily_upper]

/-- 概要：同じ四角柱の各時刻の下側は同じ正規化族のその時刻。
方針：全族の厳密制限を指定頂点で評価する。
規約：正規化前の族と取り違えない。
使われ方：可逆比較による元の下側への復帰。 -/
theorem verdierNormalizedSquareFamily_vertex_lower (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierNormalizedSquareFamily N F hdiag) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex N k := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierNormalizedSquareFamily_lower]

/-- 概要：実 Verdier 入力から正規化下側を保持した全四角柱が存在する。
方針：同じ実供給の上下族と厳密共有対角を押し出しで貼る。
規約：供給命題の追加仮定なし。元の下側との全関手同型も保持する。
使われ方：K-6 c4 の残る指定有限端点・可逆縦辺の照合の実入力。 -/
theorem verdierNormalizedSquareFamily_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ∃ (N F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (Q : ((Δ[1] ⊗ Δ[1]) ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ F = verdierMovingUpperHorn d ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ Q = F ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ Q = N := by
  obtain ⟨N, F, hN, hNhorn, hFhorn, hdiag⟩ := verdierMovingSharedDiagonal_exists d
  exact ⟨N, F, verdierNormalizedSquareFamily N F hdiag, hN, hNhorn, hFhorn,
    verdierNormalizedSquareFamily_upper N F hdiag,
    verdierNormalizedSquareFamily_lower N F hdiag⟩

end SerrePositivity.KST.Fibration
