module

public import SerrePositivity.AlgebraicGeometry.FullCechNonemptySupportIso
public import SerrePositivity.AlgebraicGeometry.NilImmersionAffineSectionCoefficients
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：nil 閉厚化の実際の引き戻しは、完全化した構造層の Čech 複体で同型。
方針：非空アフィン交叉の切断の普遍同相と、同じ逆像被覆の比較を使う。
規約：被覆の全射性・有限性や Noether 性は仮定しない。
使われ方：閉厚化の同じタプル被覆の移送（計画 N03）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- nil 閉厚化の完全構造層の Čech 引き戻しは同型。 -/
theorem nilImmersion_perfectCechPullback_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : ℕ) (hp : p.Prime)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (schemeStructurePerfectCechPullbackMap f p hp hY hX U) := by
  let η := openCoverCechCoefficientMap
    (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U
  haveI : IsIso (fullCechComplexMap η) := by
    apply fullCechComplexMap_isIso_of_nonempty_support
    intro T hT
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (frobeniusDirectLimitMap p hp
      (hY (op (cechOpenIntersection U T)))
      (hX (op (f ⁻¹ᵁ cechOpenIntersection U T)))
      (f.app (cechOpenIntersection U T)).hom)
    exact frobeniusDirectLimitUniversalHomeomorphism_bijective p hp _ _ _
      (nilImmersion_app_universalHomeomorphism f _
        (cechOpenIntersection_isAffineOpen U hU T hT))
  change IsIso (fullCechComplexMap η ≫ (schemeCechPreimageComplexIso f _ U).hom)
  infer_instance

end SerrePositivity.AlgebraicGeometry
