module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # 元の二軸 Yoneda 円錐比較のホモトピー圏同型
概要：同じ円錐比較の準同型性を、実射影的加群のホモトピー圏同型へ持ち上げる。
方針：元の代表加群とその円錐のホモトピー射影性を使う。
規約：元の比較射を順射として保持。使われ方：同じ二軸射を持つ distinguished 三角形。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToHomotopy R G

/-- 元の同じ円錐比較のホモトピー圏での像は可逆。 -/
lemma dgGluingAxesYonedaConeComparison_isIso_homotopy :
    IsIso ((Q).map (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X)) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy R G
    (moduleHomotopicallyProjective_cone R G
      (representable_homotopicallyProjective R G
        (dgGluingRightAxisObject R C D M zc X.right))
      (representable_homotopicallyProjective R G X)
      (dgGluingAxesYonedaRightMap R C D M zc hc X))
    (representable_homotopicallyProjective R G (dgGluingLeftAxisObject R C D M zd X.left))
    (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X)
    (dgGluingAxesYonedaConeComparison_moduleQuasiIso R C D M zc hc zd hd X)

/-- 同じ元の比較射を順射に持つ、円錐から左軸代表への実ホモトピー圏同型。 -/
def dgGluingAxesYonedaConeHomotopyIso :
    (Q).obj (moduleCone R G (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≅
      (Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingLeftAxisObject R C D M zd X.left))) := by
  let := dgGluingAxesYonedaConeComparison_isIso_homotopy R C D M zc hc zd hd X
  exact asIso ((Q).map (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X))

/-- 同じ実同型の順射は、元の Yoneda 円錐比較の像そのもの。 -/
lemma dgGluingAxesYonedaConeHomotopyIso_hom :
    (dgGluingAxesYonedaConeHomotopyIso R C D M zc hc zd hd X).hom =
      (Q).map (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X) := rfl

/-- 同じ円錐包含と同型の合成は、元の左軸射の Yoneda 像を回収する。 -/
lemma dgGluingAxesYonedaConeHomotopyIso_inr :
    (Q).map (moduleConeInr R G (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≫
      (dgGluingAxesYonedaConeHomotopyIso R C D M zc hc zd hd X).hom =
      (Q).map (dgGluingAxesYonedaLeftMap R C D M zd hd X) := by
  rw [dgGluingAxesYonedaConeHomotopyIso_hom, ← Functor.map_comp,
    dgGluingAxesYonedaConeComparison_inr]

end SerrePositivity.KST.SConstruction
