module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutExtremaReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：交差する path の左座標から右座標へ、同じ edgewise 重みの中で移動する。
方針：最初の一頂点を反転した左座標と、最後の零頂点の右座標を区間で結ぶ。
規約：重み全体を使い、左右の射影や Hom の Kan 性を同一視しない。
使われ方：混合 Hom の prism の交差部分を全単体で評価する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 区間の零端で左の最初の一頂点、一端で右の最後の零頂点を取る。 -/
def pathCutEdgewiseCoordinate {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (b : Fin 2) : Fin (n + n + 1 + 1) :=
  if b = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P)
  else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P)

/-- path の包含と区間の時間を同時に増やすと、重み内の座標は増加する。 -/
lemma pathCutEdgewiseCoordinate_mono {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {P Q : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)}
    (hPQ : P.I ⊆ Q.I) {b c : Fin 2} (hbc : b ≤ c) :
    pathCutEdgewiseCoordinate t hi hj P b ≤ pathCutEdgewiseCoordinate t hi hj Q c := by
  by_cases hb : b = 0 <;> by_cases hc : c = 0
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_antitone t hj hPQ
    simp only [pathCutEdgewiseCoordinate, hb, hc, ite_true]
    change n - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P).val ≤ n - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj Q).val
    exact Nat.sub_le_sub_left (show (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj Q).val ≤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P).val from h) n
  · simp only [pathCutEdgewiseCoordinate, hb, hc, ite_true, ite_false]
    change n - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P).val ≤ n + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi Q).val
    omega
  · have he : c < b := by omega
    exact False.elim (not_lt_of_ge hbc he)
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_mono t hi hPQ
    simp only [pathCutEdgewiseCoordinate, hb, hc, ite_false]
    change n + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P).val ≤ n + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi Q).val
    omega

/-- 交差 path の旗と区間を、同じ edgewise 重みの標準単体へ写す実際の prism。 -/
def pathCutEdgewisePrism {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    (Δ[1] : SSet.{u}) ⊗ nerve
      (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ Δ[n + n + 1] where
  app d := ↾fun ⟨s, P⟩ => stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    { toFun := fun k => pathCutEdgewiseCoordinate t hi hj (P.obj k)
        ((stdSimplex.objEquiv s).toOrderHom k)
      monotone' := by
        intro k l hkl
        exact pathCutEdgewiseCoordinate_mono t hi hj (P.map (homOfLE hkl)).1.1.1
          ((stdSimplex.objEquiv s).toOrderHom.monotone hkl) })
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, P⟩
    apply stdSimplex.ext
    intro k
    rfl

/-- 零端の左座標だけを取る path の関手。 -/
def pathCutEdgewiseLeftFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      ULift.{u} (Fin (n + n + 1 + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P))
  map f := homOfLE (by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_antitone t hj f.1.1.1
    change n - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj _).val ≤ n - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj _).val
    exact Nat.sub_le_sub_left (show (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj _).val ≤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj _).val from h) n)

/-- 一端の右座標だけを取る path の関手。 -/
def pathCutEdgewiseRightFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      ULift.{u} (Fin (n + n + 1 + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi P))
  map f := homOfLE (by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_mono t hi f.1.1.1
    change n + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi _).val ≤ n + 1 + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi _).val
    exact Nat.add_le_add_left h (n + 1))

/-- 同じ prism の零端は反転した左座標への射。 -/
lemma pathCutEdgewisePrism_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ pathCutEdgewisePrism t hi hj =
      nerveMap (pathCutEdgewiseLeftFunctor t (i := i) hj) ≫
        (stdSimplex.isoNerve (n + n + 1)).inv := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  rfl

/-- 同じ prism の一端は元の右座標への射。 -/
lemma pathCutEdgewisePrism_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ pathCutEdgewisePrism t hi hj =
      nerveMap (pathCutEdgewiseRightFunctor t (j := j) hi) ≫
        (stdSimplex.isoNerve (n + n + 1)).inv := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  rfl

/-- 任意の Hom の共通解像の単体を、同じ重み内の混合 prism で評価する。 -/
def pathCutEdgewiseHomPrism {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    (Δ[1] : SSet.{u}) ⊗ nerve
      (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ H :=
  pathCutEdgewisePrism t hi hj ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).inv ≫ σ

/-- 評価した混合 prism は Hom のパラメーターへの後合成と厳密に可換。 -/
lemma pathCutEdgewiseHomPrism_post {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H K : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) (f : H ⟶ K) :
    pathCutEdgewiseHomPrism t hi hj σ ≫ f =
      pathCutEdgewiseHomPrism t hi hj ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f).app _ σ) := by
  simp only [pathCutEdgewiseHomPrism, Category.assoc]
  rfl

/-- 評価した混合 prism の零端は同じ Hom 単体の左座標評価。 -/
lemma pathCutEdgewiseHomPrism_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ pathCutEdgewiseHomPrism t hi hj σ =
      nerveMap (pathCutEdgewiseLeftFunctor t (i := i) hj) ≫
        (stdSimplex.isoNerve (n + n + 1)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).inv ≫ σ := by
  rw [pathCutEdgewiseHomPrism, ← Category.assoc, pathCutEdgewisePrism_zero, Category.assoc]

/-- 評価した混合 prism の一端は同じ Hom 単体の右座標評価。 -/
lemma pathCutEdgewiseHomPrism_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ pathCutEdgewiseHomPrism t hi hj σ =
      nerveMap (pathCutEdgewiseRightFunctor t (j := j) hi) ≫
        (stdSimplex.isoNerve (n + n + 1)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).inv ≫ σ := by
  rw [pathCutEdgewiseHomPrism, ← Category.assoc, pathCutEdgewisePrism_one, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
