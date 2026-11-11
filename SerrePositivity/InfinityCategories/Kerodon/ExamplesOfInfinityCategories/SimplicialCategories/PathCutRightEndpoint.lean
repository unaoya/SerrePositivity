module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutStage
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFront

/-!
概要：混合 Hom の右端を、元の右射影と既存の切断最大座標へ戻す。
方針：最後の零頂点の射を作り、右重みへの包含と元の前面の path を照合する。
規約：全次数の Hom の評価そのものの等式を示す。
使われ方：補間段階の右端と coherentHomComparison の区間族の同定。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 最後の零頂点を選ぶ path の関手。 -/
def pathCutLastZeroFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤ ULift.{u} (Fin (n + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P)
  map f := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_mono t hi f.1.1.1)

/-- 最後の零頂点の選択を標準単体への射へ実現する。 -/
def pathCutLastZeroMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ Δ[n] :=
  nerveMap (pathCutLastZeroFunctor t hi j) ≫ (stdSimplex.isoNerve n).inv

/-- 補間の一段階の重み座標は、最後の零頂点を右半分へ含めた座標。 -/
lemma pathCutEdgewiseStageCoordinateMap_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageCoordinateMap t (OrderHom.const _ 1) hi hj =
      pathCutLastZeroMap t hi j ≫
        stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n n)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  rfl

/-- 補間の右端の Hom 評価は、元の Hom 単体の右射影を同じ最大座標で評価したもの。 -/
lemma pathCutEdgewiseStageMap_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap t (OrderHom.const _ 1) hi hj σ =
      pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight H).app _ σ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap, pathCutEdgewiseStageCoordinateMap_one,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f => pathCutLastZeroMap t hi j ≫ f)
    (SSet.yonedaEquiv.symm_apply_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ σ)).symm

/-- 前面の path の像に取った旧最大座標は、元の最後の零頂点に一致する。 -/
lemma pathCutLastZero_eq_castMaximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (R : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (hP : P.I = (fun k : ULift.{u} (Fin (n + 1)) => ULift.up k.down.castSucc) '' R.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi R = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P := by
  apply le_antisymm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum t hi P _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).1
    rw [hP]
    exact ⟨ULift.up _, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R).2, rfl⟩
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi P).2
    rw [hP] at hm
    obtain ⟨⟨k⟩, hk, he⟩ := hm
    have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P := by
      apply Fin.castSucc_inj.mp
      exact congrArg ULift.down he
    rw [← he']
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi R k
      (he' ▸ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi P).1) hk

/-- 最後の零頂点の射は、元の前面の添字写像に旧最大座標を続けた射そのもの。 -/
lemma pathCutLastZeroMap_front {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    pathCutLastZeroMap t hi j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningDirectHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro R
  apply stdSimplex.ext
  intro k
  exact pathCutLastZero_eq_castMaximum t hi (R.obj k) _ rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
