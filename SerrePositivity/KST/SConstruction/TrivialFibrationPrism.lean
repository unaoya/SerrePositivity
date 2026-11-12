module
public import SerrePositivity.KST.SConstruction.ZeroNaturalTransformations
public import SerrePositivity.KST.SConstruction.TrivialFibrationUniversality

/-! # 自明ファイブレーションによる両端指定 prism の持ち上げ
概要：両端の持ち上げを指定した任意の prism を自明ファイブレーションで持ち上げる。
方針：区間境界とパラメーターの積の単射に対する RLP を使う。
規約：持ち上げを可逆な変換とは主張しない。使われ方：McCarthy の λ→ν の変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

private lemma boundaryDiagram_postcomp {A E B : SSet.{u}} (f g : A ⟶ E) (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ p) (g ≫ p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  change p.app (Opposite.op ⦋n⦌) (if t.val 0 = 0 then f.app _ a else g.app _ a) =
    if t.val 0 = 0 then p.app _ (f.app _ a) else p.app _ (g.app _ a)
  split_ifs <;> rfl

/-- 概要：指定した両端を厳密に保持して prism を自明ファイブレーションで持ち上げられる。
方針：区間境界の積の単射に対する持ち上げ性。
規約：全ての単体集合とパラメーターを許す。使われ方：cofiber の射の coherent な変換。 -/
lemma exists_lift_prism_of_trivialKanFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ p) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ F = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ F = g ∧ F ≫ p = H := by
  let i := (boundary 1).ι ▷ A
  have : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [mono_iff_injective]
    rintro ⟨t, a⟩ ⟨s, b⟩ h
    change (t.val, a) = (s.val, b) at h
    have ht : t.val = s.val := congrArg
      (fun x : (Δ[1] : SSet.{u}).obj d × A.obj d => x.1) h
    have ha : a = b := congrArg
      (fun x : (Δ[1] : SSet.{u}).obj d × A.obj d => x.2) h
    exact Prod.ext (Subtype.ext ht) ha
  have hsq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ p = i ≫ H := by
    rw [boundaryDiagram_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, h₀, h₁]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) i inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g) i p H := ⟨hsq⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0 A, Category.assoc, sq.fac_left,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1 A, Category.assoc, sq.fac_left,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

/-- 概要：両端を指定した prism の持ち上げを一つ選ぶ。
方針：自明ファイブレーションの相対持ち上げの存在から選ぶ。
規約：同じパラメーター全体に一つの持ち上げ。使われ方：McCarthy の λ→ν の実際の射。 -/
def liftPrismOfTrivialKanFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ p) :
    (Δ[1] : SSet.{u}) ⊗ A ⟶ E :=
  Classical.choose (exists_lift_prism_of_trivialKanFibration p f g H h₀ h₁)

/-- 概要：選んだ prism の持ち上げの始点は指定した f。
方針：選択の仕様の第一成分。
規約：厳密な等号。使われ方：λ の端点。 -/
lemma liftPrismOfTrivialKanFibration_zero {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ liftPrismOfTrivialKanFibration p f g H h₀ h₁ = f :=
  (Classical.choose_spec (exists_lift_prism_of_trivialKanFibration p f g H h₀ h₁)).1

/-- 概要：選んだ prism の持ち上げの終点は指定した g。
方針：選択の仕様の第二成分。
規約：厳密な等号。使われ方：ν の端点。 -/
lemma liftPrismOfTrivialKanFibration_one {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ liftPrismOfTrivialKanFibration p f g H h₀ h₁ = g :=
  (Classical.choose_spec (exists_lift_prism_of_trivialKanFibration p f g H h₀ h₁)).2.1

/-- 概要：選んだ prism の持ち上げは指定した基底の prism を厳密に覆う。
方針：選択の仕様の第三成分。
規約：全パラメーターでの等号。使われ方：subobject と middle の変換の制御。 -/
lemma liftPrismOfTrivialKanFibration_projection {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ p) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ p) :
    liftPrismOfTrivialKanFibration p f g H h₀ h₁ ≫ p = H :=
  (Classical.choose_spec (exists_lift_prism_of_trivialKanFibration p f g H h₀ h₁)).2.2

end SerrePositivity.KST.SConstruction
