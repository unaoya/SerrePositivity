module
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedModel
public import SerrePositivity.InfinityCategories.Derived.ComplexQuasiIsoSpan
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapTrivialFibration
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-! # 複体の実 pinched 模型の一般準同型不変性

概要：次数ごとの全射性を要求しない準同型は、実 pinched 模型のホモトピー同値。
方針：比較複体からの二つの全射準同型の実境界充填と、実切断の等式を使う。
規約：模型圏の仮定なし。使われ方：商の Hom 比較と dg nerve の充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded CochainComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

/-- 全射準同型は実 pinched 模型上の自明 Kan fibration を与える。 -/
lemma complexPinchedMap_trivialKanFibration (φ : K ⟶ L)
    (hs : ∀ i, Function.Surjective (φ.f i)) [QuasiIso φ] :
    TrivialKanFibration (complexPinchedMap.{u, v} φ) :=
  pinchedHomChainMap_trivialKanFibration _ (complexUnitHomPostcompose_surjective φ hs)
    (complexUnitHomPostcompose_quasiIso φ)

/-- 任意の準同型は、同じ宇宙の実 pinched 模型のホモトピー同値を誘導する。 -/
theorem complexPinchedMap_quasiIso_equivalence (φ : K ⟶ L) [QuasiIso φ] :
    IsSimplicialHomotopyEquivalence (complexPinchedMap.{u, v} φ) := by
  let l := complexQuasiIsoSpanLeft φ
  let r := complexQuasiIsoSpanRight φ
  let s := complexQuasiIsoSpanSection φ
  let : QuasiIso l := complexQuasiIsoSpanLeft_quasiIso φ
  let : QuasiIso r := complexQuasiIsoSpanRight_quasiIso φ
  let : TrivialKanFibration (complexPinchedMap.{u, v} l) :=
    complexPinchedMap_trivialKanFibration l (complexQuasiIsoSpanLeft_surjective φ)
  let : TrivialKanFibration (complexPinchedMap.{u, v} r) :=
    complexPinchedMap_trivialKanFibration r (complexQuasiIsoSpanRight_surjective φ)
  have hl := isQCatEquivalence_of_trivialKanFibration (complexPinchedMap.{u, v} l)
  have hr := isQCatEquivalence_of_trivialKanFibration (complexPinchedMap.{u, v} r)
  have hs : IsQCatEquivalence (complexPinchedMap.{u, v} s) := by
    apply hl.cancel_right
    rw [← complexPinchedMap_comp]
    change IsQCatEquivalence (complexPinchedMap.{u, v}
      (complexQuasiIsoSpanSection φ ≫ complexQuasiIsoSpanLeft φ))
    simp only [complexQuasiIsoSpanSection, complexQuasiIsoSpanLeft, biprod.inl_fst,
      complexPinchedMap_id]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  have he := hs.comp hr
  rw [← complexPinchedMap_comp, complexQuasiIsoSpanSection_right] at he
  exact he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
