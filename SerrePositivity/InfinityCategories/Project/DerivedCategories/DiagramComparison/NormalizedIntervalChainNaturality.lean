module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalRawChain
/-!
概要：指定区間の鎖評価は標的複体の射で可換になる。
方針：元の自由鎖の零・一次を生成元で計算し、同じ包含を前合成する。
規約：A06自然性の証明分割。型に境界条件を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 同じ自由区間評価の後合成自然性。 -/
theorem intervalRawChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalRawChainMap A K x y w hw ≫ q =
      intervalRawChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw' := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change intervalVertexEvaluation A (K.X 0) x y ≫ q.f 0 = _
    apply ModuleCat.free_hom_ext
    intro a
    simp only [ModuleCat.comp_apply]
    dsimp only [intervalVertexEvaluation]
    repeat' erw [ModuleCat.freeDesc_apply]
    change q.f 0 (intervalVertexValue x y ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0)) =
      intervalVertexValue (q.f 0 x) (q.f 0 y) ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0)
    unfold intervalVertexValue
    split <;> rfl
  | succ n =>
    cases n with
    | zero =>
      change intervalEdgeEvaluation A (K.X 1) w ≫ q.f 1 = _
      apply ModuleCat.free_hom_ext
      intro a
      simp only [ModuleCat.comp_apply]
      dsimp only [intervalEdgeEvaluation]
      repeat' erw [ModuleCat.freeDesc_apply]
      change q.f 1 (intervalEdgeValue w ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0)
        ((SSet.stdSimplex.objEquiv a.down).toOrderHom 1)) =
        intervalEdgeValue (q.f 1 w) ((SSet.stdSimplex.objEquiv a.down).toOrderHom 0)
          ((SSet.stdSimplex.objEquiv a.down).toOrderHom 1)
      unfold intervalEdgeValue
      split
      · rfl
      · exact map_zero _
    | succ n =>
      change (0 : _ ⟶ K.X (n + 2)) ≫ q.f (n + 2) = 0
      exact CategoryTheory.Limits.zero_comp
/-- 同じ包含を前合成した正規化区間評価の自然性。 -/
theorem intervalNormalizedChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalNormalizedChainMap A K x y w hw ≫ q =
      intervalNormalizedChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw' := by
  dsimp only [intervalNormalizedChainMap]
  rw [Category.assoc, intervalRawChainMap_postcomp A q x y w hw hw']
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
