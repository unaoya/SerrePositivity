module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGSuspensionNativeSquareModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaNativePComparison

/-!
概要：同じ全四角形と実評価 Morita 全族から、元の P 比較の全族までを保持する型。
方針：四角形・厳密豊穣懸垂作用・実 Morita 比較をデータにし、P 全族は既存比較から構成する。
規約：型の存在は未証明。元の I・P・ν・K と選択四角形全体を変えない。
元の導来模型における P.inclusion 自体の全入力比較は、この型だけで供給済みと数えない。
使われ方：K-B3 へ公開する四角形・Morita 全族の型と、P/Yoneda 全入力比較の導出。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 同じ実四角形と実評価 Morita 作用の全入力自然性。
元の P の全入力比較は、このデータから追加入力なしで導かれる。存在は未供給。 -/
structure DGSuspensionNativeNaturalityModel extends _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeSquareModel R s where
  /-- 元の同じ実評価 Morita 逆作用を全 native 入力上で保持する族。 -/
  morita : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}
  /-- 始点は元の固定 ν の全作用そのもの。 -/
  morita_source : morita ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    dgKInputNu R
  /-- 終点は同じ全四角形の実核角に固定 ν を続けた全作用。 -/
  morita_target : morita ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    dgSuspensionNativeSquareCornerFamily R square 0 0 ≫ dgKInputNu R
  /-- 各入力では、元の同じ選択実評価 Morita 比較の全一単体を厳密に回収する。 -/
  morita_at : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    morita.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge)

variable (m : DGSuspensionNativeNaturalityModel R s)

/-- 同じ全 Morita 族の全入力点は、固定 ν の源内の可逆な辺である。 -/
lemma DGSuspensionNativeNaturalityModel.morita_isEquivalencePathVertex
    (k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (m.morita.app (Opposite.op ⦋0⦌) k) := by
  obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv
    (PerfDGInput.{u, max (u + 1) v} R)).surjective k
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (m.morita.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A))
  rw [m.morita_at]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mpr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R A (s A).cone (s A).perfect)

/-- 固定 ν と同じ実核角の固定 ν の、全 native 入力に自然な実同型。 -/
def DGSuspensionNativeNaturalityModel.moritaIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputNu R)
      (dgSuspensionNativeSquareCornerFamily R m.square 0 0 ≫ dgKInputNu R) := by
  let H := uncurry m.morita
  have hi (k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max (u + 1) v + 1})),
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1))) := by
    have hk := m.morita_isEquivalencePathVertex R s k
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hk
    rw [← curry_uncurry m.morita, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hk
    exact hk
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy H hi
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval H 0, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval H 1] at e
  dsimp only [H] at e
  rw [curry_uncurry, m.morita_source, m.morita_target] at e
  exact e

/-- 元の P 比較の全 native 入力族。元の指定比較以外の自然性入力は使わない。 -/
def DGSuspensionNativeNaturalityModel.perfectComparison :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists R s m.morita m.morita_at).choose

/-- 元の P と元の Yoneda の合成による包含の全 native 入力族。 -/
def DGSuspensionNativeNaturalityModel.perfectFamily :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶
      (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  m.perfectComparison R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0

/-- P の全比較は元の同じ全 Morita 族へ終わる。 -/
theorem DGSuspensionNativeNaturalityModel.perfectComparison_one :
    m.perfectComparison R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 = m.morita :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists R s m.morita m.morita_at).choose_spec.2.1

/-- P の比較は、両端の全入力作用上で恒等 path そのもの。 -/
theorem DGSuspensionNativeNaturalityModel.perfectComparison_boundary :
    m.perfectComparison R s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}) =
        (m.morita ≫ (pre (boundary 1).ι).app _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists R s m.morita m.morita_at).choose_spec.1

/-- 各入力で元の指定 P 比較 path 自体を厳密に回収する。 -/
theorem DGSuspensionNativeNaturalityModel.perfectComparison_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (m.perfectComparison R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonPath R A (s A).cone (s A).perfect :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists R s m.morita m.morita_at).choose_spec.2.2.1 A

/-- 各入力で元の P と元の Yoneda の全包含を厳密に回収する。 -/
theorem DGSuspensionNativeNaturalityModel.perfectFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (m.perfectFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePExactMap R A (s A).cone (s A).perfect)).edge) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists R s m.morita m.morita_at).choose_spec.2.2.2 A

/-- 元の P の包含は両 ν 端を、全単体で元の Morita 族と厳密に共有する。 -/
theorem DGSuspensionNativeNaturalityModel.perfectFamily_boundary :
    m.perfectFamily R s ≫ (pre (boundary 1).ι).app _ =
      m.morita ≫ (pre (boundary 1).ι).app _ := by
  rw [DGSuspensionNativeNaturalityModel.perfectFamily, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc, m.perfectComparison_boundary]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
