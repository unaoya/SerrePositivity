module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofRelativeCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition

/-! # 比較と動く境界を保つ二段階輸送の合成

概要：元境界と商全体の二段階輸送を、合成二単体ごと厳密に整合させる。
方針：元境界の合成三角形を先に選び、その商像を指定して全体の合成三角形を持ち上げる。
規約：境界の各輸送も合成後の輸送も定値とは仮定しない。使われ方：実屋根の相対充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {L K E Q : SSet.{u}} (i : L ⟶ K) (F : E ⟶ Q)
variable {a₀ a₁ a₂ : L ⟶ E} {g₀ g₁ g₂ : K ⟶ Q}
variable (lA : SSet.Homotopy a₀ a₁) (rA : SSet.Homotopy a₁ a₂)
variable (lK : SSet.Homotopy g₀ g₁) (rK : SSet.Homotopy g₁ g₂)

/-- 境界と全体を比較に沿って同じ実二単体で整合させた合成。 -/
structure RoofCompatibleTransportComposite where
  source : SSet.Homotopy a₀ a₂
  target : SSet.Homotopy g₀ g₂
  sourceTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle lA rA source
  targetTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle lK rK target
  triangle_boundary : targetTriangle.diagram ≫ (pre i).app Q =
    sourceTriangle.diagram ≫ (ihom L).map F

variable {i F lA rA lK rK}

/-- 合成後の二輸送は境界全体・全時刻で比較と厳密に一致する。 -/
lemma RoofCompatibleTransportComposite.boundary
    (C : RoofCompatibleTransportComposite i F lA rA lK rK) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ C.target.h = C.source.h ≫ F := by
  have h := congrArg (fun D => stdSimplex.δ (1 : Fin 3) ≫ D) C.triangle_boundary
  rw [← Category.assoc, C.targetTriangle.face_one, ← Category.assoc,
    C.sourceTriangle.face_one] at h
  have hu := congrArg uncurry h
  rw [uncurry_pre_app, uncurry_natural_right, uncurry_curry, uncurry_curry] at hu
  exact hu

/-- 二つの比較整合的な輸送は、動く境界と実合成二単体を保って同時合成できる。 -/
theorem roofCompatibleTransportComposite_nonempty [Quasicategory E] [Quasicategory Q] [Mono i]
    (hl : (i ▷ (Δ[1] : SSet.{u})) ≫ lK.h = lA.h ≫ F)
    (hr : (i ▷ (Δ[1] : SSet.{u})) ≫ rK.h = rA.h ≫ F) :
    Nonempty (RoofCompatibleTransportComposite i F lA rA lK rK) := by
  obtain ⟨s, Ts⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_functorHomotopyComposite lA rA
  let D := Ts.some.diagram ≫ (ihom L).map F
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry rK.h ≫ (pre i).app Q := by
    change stdSimplex.δ (0 : Fin 3) ≫ (Ts.some.diagram ≫ (ihom L).map F) = _
    rw [← Category.assoc, Ts.some.face_zero]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hr.symm
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry lK.h ≫ (pre i).app Q := by
    change stdSimplex.δ (2 : Fin 3) ≫ (Ts.some.diagram ≫ (ihom L).map F) = _
    rw [← Category.assoc, Ts.some.face_two]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hl.symm
  obtain ⟨t, Tt, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.roofRelativeCompositionTriangle_exists i lK rK D h₀ h₂
  exact ⟨⟨s, t, Ts.some, Tt, hT⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
