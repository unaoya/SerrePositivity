module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaNativePComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeEquivalencePathExtension

/-!
概要：元の実評価 Morita 辺の全族を、固定 ν を始点として実構成する。
方針：可逆 path の始点評価の自明 Kan 性で、全入力の零骨格上の実辺を延長する。
規約：終点はこの延長で構成する StableInfinity 値の作用である。固定 S 内の核作用、
その ν 像との一致、懸垂作用、全四角形の存在は主張しない。模型・I・P は変更しない。
使われ方：D-8 e の実 Morita 全族と、元の P/Yoneda 全比較の構成部品。
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

/-- 同じ実評価 Morita 辺を全入力で延長し、始点 ν と各対象の全実辺を厳密に保つ。 -/
lemma dgKappaNativeMoritaFamily_exists :
    ∃ L : dgKInputInfinity.{u, max (u + 1) v} R ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v},
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = dgKInputNu R ∧
      ∀ A : PerfDGInput.{u, max (u + 1) v} R,
        L.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
            (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R A (s A).cone (s A).perfect) := by
  let a := fun k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌ =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)
        (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).cone (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).perfect))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)
        (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).cone (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).perfect)
  have hav (A : PerfDGInput.{u, max (u + 1) v} R) :
      a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R A (s A).cone (s A).perfect) := by
    dsimp only [a]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject_vertex]
  have ha : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (a k) =
      (dgKInputNu R).app (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
      (a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) =
        (dgKInputNu R).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
    rw [hav, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_zero, dgKInputNu_vertex]
  have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (dgKInputInfinity.{u, max (u + 1) v} R))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0) (dgKInputNu R) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp _ _ a ha⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  intro A
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
  change sq.lift.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) 0) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) 0 at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, hav] using h

/-- 実構成した全 Morita 比較。終点の S 内核作用への持ち上げは別工程。 -/
def dgKappaNativeMoritaFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  (dgKappaNativeMoritaFamily_exists R s).choose

lemma dgKappaNativeMoritaFamily_source :
    dgKappaNativeMoritaFamily R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = dgKInputNu R :=
  (dgKappaNativeMoritaFamily_exists R s).choose_spec.1

lemma dgKappaNativeMoritaFamily_at (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R A (s A).cone (s A).perfect) :=
  (dgKappaNativeMoritaFamily_exists R s).choose_spec.2 A

/-- 元の実辺を各対象で厳密回収する、全 native 入力の arrow 値比較族。 -/
def dgKappaNativeMoritaArrowFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  dgKappaNativeMoritaFamily R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι _

lemma dgKappaNativeMoritaArrowFamily_at (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaNativeMoritaArrowFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι _).app (Opposite.op ⦋0⦌)
    ((dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [dgKappaNativeMoritaFamily_at]
  rfl

/-- 全入力で構成した実核の StableInfinity 値。S 内の核作用はまだ構成しない。 -/
def dgKappaNativeKernelStableFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  dgKappaNativeMoritaFamily R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1

lemma dgKappaNativeKernelStableFamily_at (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaNativeKernelStableFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R (dgKappaResolvedKernelKInput R A (s A).cone)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
    ((dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [dgKappaNativeMoritaFamily_at, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_one]

/-- 固定 ν と構成した実核 StableInfinity 値との、全 native 入力に自然な実同型。 -/
def dgKappaNativeMoritaFamily_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputNu R) (dgKappaNativeKernelStableFamily R s) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanEquivalencePath_functorIso (dgKappaNativeMoritaFamily R s)
  rw [dgKappaNativeMoritaFamily_source] at h
  exact h

/-- arrow 表示でも、始点は固定 ν の全作用そのもの。 -/
lemma dgKappaNativeMoritaArrowFamily_source :
    dgKappaNativeMoritaArrowFamily R s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = dgKInputNu R := by
  change dgKappaNativeMoritaFamily R s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = _
  exact dgKappaNativeMoritaFamily_source R s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
