module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.ComplexPinchedModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexQuasiIsoSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-! # 複体の実 pinched 模型の一般準同型不変性

概要：次数ごとの全射性を要求しない準同型は、実 pinched 模型のホモトピー同値。
方針：比較複体からの二つの全射準同型の実境界充填と、実切断の等式を使う。
規約：模型圏の仮定なし。使われ方：商の Hom 比較と dg nerve の充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded CochainComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

/-- 全射準同型は実 pinched 模型上の自明 Kan fibration を与える。 -/
lemma complexPinchedMap_trivialKanFibration (φ : K ⟶ L)
    (hs : ∀ i, Function.Surjective (φ.f i)) [QuasiIso φ] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_trivialKanFibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomPostcompose_surjective φ hs)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomPostcompose_quasiIso φ)

/-- 任意の準同型は、同じ宇宙の実 pinched 模型のホモトピー同値を誘導する。 -/
theorem complexPinchedMap_quasiIso_equivalence (φ : K ⟶ L) [QuasiIso φ] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) := by
  let l := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft φ
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight φ
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection φ
  let : QuasiIso l := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft_quasiIso φ
  let : QuasiIso r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight_quasiIso φ
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} l) :=
    complexPinchedMap_trivialKanFibration l (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft_surjective φ)
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} r) :=
    complexPinchedMap_trivialKanFibration r (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight_surjective φ)
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} l)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} r)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} s) := by
    apply hl.cancel_right
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection φ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft φ))
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft, biprod.inl_fst,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  have he := hs.comp hr
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection_right] at he
  exact he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
