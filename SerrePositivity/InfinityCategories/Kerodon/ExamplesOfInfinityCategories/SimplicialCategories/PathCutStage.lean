module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutEdgewisePrism

/-!
概要：混合 Hom の補間段階を、元の単体の区間パラメーターで指定する。
方針：最後の零頂点で段階を読み、同じ path の左右の座標を選ぶ。
規約：段階の単調性と、同じラベル側での合成との整合性を保持する。
使われ方：混合 Hom を coherent な単体の豊穣 Hom の作用へ束ねる。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- path の最後の零頂点で段階を読み取る、重みの頂点への関手。 -/
def pathCutEdgewiseStageFunctor {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      ULift.{u} (Fin (n + n + 1 + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate t hi hj P (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P)))
  map f := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate_mono t hi hj f.1.1.1
    (s.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_mono t hi f.1.1.1)))

/-- 零に固定した補間段階は、同じ左座標の関手そのもの。 -/
lemma pathCutEdgewiseStageFunctor_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    pathCutEdgewiseStageFunctor t (OrderHom.const _ 0) hi hj =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseLeftFunctor t (i := i) hj := by
  apply CategoryTheory.Functor.ext (fun P => by rfl)

/-- 一に固定した補間段階は、同じ右座標の関手そのもの。 -/
lemma pathCutEdgewiseStageFunctor_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    pathCutEdgewiseStageFunctor t (OrderHom.const _ 1) hi hj =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseRightFunctor t (j := j) hi := by
  apply CategoryTheory.Functor.ext (fun P => by rfl)

/-- 零側での前合成は、段階を含めた混合座標を変えない。 -/
lemma pathCutEdgewiseStage_comp_zero {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    (pathCutEdgewiseStageFunctor t s hi hk).obj
      ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
        (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
      (pathCutEdgewiseStageFunctor t s hj hk).obj Q := by
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate _ _ _ _ _) = ULift.up _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_comp_zero t hi hj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_comp_zero t hj hk]

/-- 一側での後合成も、段階を含めた混合座標を変えない。 -/
lemma pathCutEdgewiseStage_comp_one {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) (hk : t k = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up j : ULift.{u} (Fin (n + 1))) (ULift.up k)) :
    (pathCutEdgewiseStageFunctor t s hi hk).obj
      ((compFunctor ⟨ULift.up i⟩ ⟨ULift.up j⟩
        (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))).obj (P, Q)) =
      (pathCutEdgewiseStageFunctor t s hi hj).obj P := by
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate _ _ _ _ _) = ULift.up _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseCoordinate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_comp_one t hi hj,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_comp_one t hj hk]

/-- 補間段階で選んだ座標を、重みの標準単体への射へ実現する。 -/
def pathCutEdgewiseStageCoordinateMap {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ Δ[n + n + 1] :=
  nerveMap (pathCutEdgewiseStageFunctor t s hi hj) ≫
    (stdSimplex.isoNerve (n + n + 1)).inv

/-- 零側の合成に対する座標の不変性は、nerve 上の射そのものの等式。 -/
lemma pathCutEdgewiseStageCoordinateMap_comp_zero {n : ℕ}
    (t s : Fin (n + 1) →o Fin 2) {i j k : Fin (n + 1)}
    (hi : t i = 0) (hj : t j = 0) (hk : t k = 1) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutEdgewiseStageCoordinateMap t s hi hk =
    CartesianMonoidalCategory.snd _ _ ≫ pathCutEdgewiseStageCoordinateMap t s hj hk := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact congrArg ULift.down (pathCutEdgewiseStage_comp_zero t s hi hj hk (P.obj l) (Q.obj l))

/-- 一側の合成に対する不変性も、nerve 上の射そのものの等式。 -/
lemma pathCutEdgewiseStageCoordinateMap_comp_one {n : ℕ}
    (t s : Fin (n + 1) →o Fin 2) {i j k : Fin (n + 1)}
    (hi : t i = 0) (hj : t j = 1) (hk : t k = 1) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutEdgewiseStageCoordinateMap t s hi hk =
    CartesianMonoidalCategory.fst _ _ ≫ pathCutEdgewiseStageCoordinateMap t s hi hj := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact congrArg ULift.down (pathCutEdgewiseStage_comp_one t s hi hj hk (P.obj l) (Q.obj l))

/-- 指定した補間段階で、共通 Hom の同じ単体を評価する射。 -/
def pathCutEdgewiseStageMap {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ H :=
  pathCutEdgewiseStageCoordinateMap t s hi hj ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).inv ≫ σ

/-- 段階ごとの評価も、Hom の射への後合成と厳密に可換。 -/
lemma pathCutEdgewiseStageMap_post {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H K : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) (f : H ⟶ K) :
    pathCutEdgewiseStageMap t s hi hj σ ≫ f =
      pathCutEdgewiseStageMap t s hi hj ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f).app _ σ) := by
  simp only [pathCutEdgewiseStageMap, Category.assoc]
  rfl

/-- 零側の合成は、共通 Hom の単体を評価した後も厳密に後半の作用となる。 -/
lemma pathCutEdgewiseStageMap_comp_zero {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) (hk : t k = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutEdgewiseStageMap t s hi hk σ =
    CartesianMonoidalCategory.snd _ _ ≫ pathCutEdgewiseStageMap t s hj hk σ := by
  rw [pathCutEdgewiseStageMap, pathCutEdgewiseStageMap, ← Category.assoc,
    pathCutEdgewiseStageCoordinateMap_comp_zero t s hi hj hk, Category.assoc]

/-- 一側の合成は、共通 Hom の単体を評価した後も厳密に前半の作用となる。 -/
lemma pathCutEdgewiseStageMap_comp_one {n : ℕ} (t s : Fin (n + 1) →o Fin 2)
    {i j k : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) (hk : t k = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ pathCutEdgewiseStageMap t s hi hk σ =
    CartesianMonoidalCategory.fst _ _ ≫ pathCutEdgewiseStageMap t s hi hj σ := by
  rw [pathCutEdgewiseStageMap, pathCutEdgewiseStageMap, ← Category.assoc,
    pathCutEdgewiseStageCoordinateMap_comp_one t s hi hj hk, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
