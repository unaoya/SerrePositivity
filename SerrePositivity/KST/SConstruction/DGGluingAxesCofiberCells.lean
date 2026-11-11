module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaHomZero

/-! # 元の二軸 cofiber の実 dg 二セル
概要：元の右軸・中央・左軸と実零対象を固定し、元の上下比較を dg nerve へ戻す。
方針：元の Yoneda Hom 同型で各比較原始元を戻し、同じ三閉射を保持する。
規約：零角は指定 gluing 零対象。使われ方：共通宇宙での実四角形の貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "A" => dgGluingRightAxisObject R C D M zc X.right
local notation "B" => dgGluingLeftAxisObject R C D M zd X.left
local notation "Z" => dgGluingRightAxisObject R C D M zc zd
local notation "s" => dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X

/-- 元の二軸間の指定三閉射と同じ比較原始元を持つ、実二単体の持ち上げ。 -/
def dgGluingAxesTriangleLift (Y : G)
    (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) Y)
    (g : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) B)
    (t : GradedHom R (representable R A) (representable R B) (-1)) :
    SSet.Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R G f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R G g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R G (0 : ForgetEnrichment.of (Complex R) A ⟶
        ForgetEnrichment.of (Complex R) B)) :=
  dgClosedTriangleHomIsoLift (dgYoneda R G) f g 0
    (dgYonedaIso R A (representable R B)).symm rfl t (by
      exact (dgGluingAxesYonedaHom_subsingleton R C D M zc hc zd hd X 0).elim _ _)

/-- 元の右軸包含・左軸射影を保持し、同じ下側比較原始元を戻した実二単体。 -/
def dgGluingAxesCofiberLowerCell :=
  dgGluingAxesTriangleLift R C D M zc hc zd hd X X
    (dgGluingAxisRightInclusion R C D M zc hc X)
    (dgGluingAxisLeftProjection R C D M zd hd X) (s).lowerHomotopy

/-- 指定実 gluing 零対象を経由し、同じ上側比較原始元を戻した実二単体。 -/
def dgGluingAxesCofiberUpperCell :=
  dgGluingAxesTriangleLift R C D M zc hc zd hd X Z 0 0 (s).upperHomotopy

end SerrePositivity.KST.SConstruction
