module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedGenerators
public import SerrePositivity.DifferentialGraded.Perfect.Generators

/-! # 指定compact生成元の下での導来Homの保守性

compact性と全整数shiftによる零対象の検出を別の成分として明示する。
導来圏全体の同値をこの段階で結論しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 指定対象自身のcompact性と、その整数shiftによる全導来対象の零性の検出。 -/
def endomorphismCompactGenerator : Prop :=
  moduleCompact A D ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ∧
    ∀ X : DerivedModuleCategory A D,
      (∀ n : ℤ, Subsingleton
        (((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ⟶ X⟦n⟧)) → IsZero X

variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE
local instance : (endomorphismDerivedHom A D E hE).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E hE

/-- compact生成仮定の検出成分と、正則End加群のtensor像の計算から零性を反映する。 -/
lemma endomorphismDerivedHom_reflectsZero (hCG : endomorphismCompactGenerator A D E)
    (X : DerivedModuleCategory A D) (hX : IsZero ((endomorphismDerivedHom A D E hE).obj X)) :
    IsZero X := by
  apply hCG.2 X
  intro n
  let R := endomorphismDerivedHom A D E hE
  let G := (moduleToDerived A (EndomorphismObject E)).obj
    (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))))
  have hz : IsZero (R.obj (X⟦n⟧)) :=
    ((shiftFunctor (DerivedModuleCategory A (EndomorphismObject E)) n).map_isZero hX).of_iso
      ((R.commShiftIso n).app X)
  let e := (Iso.homCongr (endomorphismDerivedTensor_regularIso A D E).symm
    (Iso.refl (X⟦n⟧))).trans ((endomorphismDerivedAdjunction A D E hE).homEquiv G (X⟦n⟧))
  exact ⟨fun f g => e.injective (hz.eq_of_tgt (e f) (e g))⟩

/-- 三角性と零性の反映から、実際の導来Homは同型を反映する。 -/
lemma endomorphismDerivedHom_reflectsIso (hCG : endomorphismCompactGenerator A D E)
    {X Y : DerivedModuleCategory A D} (f : X ⟶ Y)
    [IsIso ((endomorphismDerivedHom A D E hE).map f)] : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  let R := endomorphismDerivedHom A D E hE
  have hRT := R.map_distinguished T hT
  have hz : IsZero (R.obj Z) :=
    ((R.mapTriangle.obj T).isZero₃_iff_isIso₁ hRT).2 (by
      change IsIso ((endomorphismDerivedHom A D E hE).map f)
      infer_instance)
  exact (T.isZero₃_iff_isIso₁ hT).1
    (endomorphismDerivedHom_reflectsZero A D E hE hCG Z hz)

/-- 明示したcompact生成仮定の下でのみ使う保守性の型クラス。 -/
lemma endomorphismDerivedHomReflectsIsomorphisms
    (hCG : endomorphismCompactGenerator A D E) :
    (endomorphismDerivedHom A D E hE).ReflectsIsomorphisms where
  reflects f := endomorphismDerivedHom_reflectsIso A D E hE hCG f

end SerrePositivity.DifferentialGraded
