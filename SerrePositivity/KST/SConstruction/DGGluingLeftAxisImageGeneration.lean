module
public import SerrePositivity.KST.SConstruction.DGGluingAxesImageGeneration

/-! # 元の二軸三角形による左軸像の生成
概要：同じ右軸像と元の中央対象像から、元の左軸像の代表を生成する。
方針：D の実導来延長へ条件を引き戻し、元の二軸三角形の第三対象を使う。
規約：商像の生成性を仮定しない。使われ方：実対角像と右軸による具体的生成性。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) E)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToDerived R E
local instance : (dgDerivedExtension R G E F).CommShift ℤ :=
  dgDerivedExtensionCommShift R G E F
local instance : (dgDerivedExtension R G E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated R G E F

include hc hd in
/-- 元の右軸像と中央像を含む三角的条件は、同じ元の左軸像を含む。 -/
lemma dgGluingLeftAxis_image_mem_of_right_middle
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (X : G)
    (hR : P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc X.right))))))
    (hX : P ((Q).obj (ForgetEnrichment.of (Complex R) (representable R (F.obj X))))) :
    P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingLeftAxisObject R C D M zd X.left))))) := by
  let P' := P.inverseImage (dgDerivedExtension R G E F)
  have : P'.IsTriangulated := by dsimp [P']; infer_instance
  have : P'.IsClosedUnderIsomorphisms := by dsimp [P']; infer_instance
  have hr : P' ((moduleToDerived R G).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingRightAxisObject R C D M zc X.right)))) :=
    P.prop_of_iso (dgDerivedExtensionRepresentableIso R G E F
      (dgGluingRightAxisObject R C D M zc X.right)).symm hR
  have hx : P' ((moduleToDerived R G).obj
      (ForgetEnrichment.of (Complex R) (representable R X))) :=
    P.prop_of_iso (dgDerivedExtensionRepresentableIso R G E F X).symm hX
  have hl := P'.ext_of_isTriangulatedClosed₃
    (dgGluingAxesDerivedTriangle R C D M zc hc zd hd X)
    (dgGluingAxesDerivedTriangle_distinguished R C D M zc hc zd hd X) hr hx
  exact P.prop_of_iso
    (dgDerivedExtensionRepresentableIso R G E F (dgGluingLeftAxisObject R C D M zd X.left)) hl

end SerrePositivity.KST.SConstruction
