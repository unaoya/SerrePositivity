module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPinchedRepresentable
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierComposition
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # 閉零圏の実 Verdier 分母による厳密屋根図式

概要：Over(x) の実 Verdier 分母である対象へ、実 pinched Hom の反変関手を制限する。
方針：指定対象条件の充満部分圏と、始域への忘却関手を使う。
規約：通常の厳密 over 圏を使う。実 ∞ over slice との同値性は主張しない。
使われ方：元の分母の細分図式と実写像空間の局所化比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉零圏の over 対象が指定された実 Verdier 分母である条件。 -/
def dgClosedVerdierDenominatorProperty (P : Set D) (x : D) :
    ObjectProperty (Over (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) :=
  fun s => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s.hom).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P

/-- 指定された元の実 Verdier 分母の厳密 over 圏。 -/
abbrev DGClosedVerdierDenominators (P : Set D) (x : D) :=
  (dgClosedVerdierDenominatorProperty A D P x).FullSubcategory

/-- 厳密分母から、その元の閉零始域への忘却関手。 -/
def dgClosedVerdierDenominatorSource (P : Set D) (x : D) :
    DGClosedVerdierDenominators A D P x ⥤ ClosedCategory A D :=
  (dgClosedVerdierDenominatorProperty A D P x).ι ⋙ Over.forget _

/-- 各実分母の始域から y への実 pinched Hom を取る、厳密屋根の反変図式。 -/
def dgClosedVerdierRoofDiagram (P : Set D) (x y : D) :
    (DGClosedVerdierDenominators A D P x)ᵒᵖ ⥤ SSet.{max u v} :=
  (dgClosedVerdierDenominatorSource A D P x).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPinchedRepresentable A D y

/-- 指定された元の実分母から、厳密屋根図式の添字対象を得る。 -/
def dgClosedVerdierDenominatorMk (P : Set D) {q x : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    DGClosedVerdierDenominators A D P x := ⟨Over.mk s, hs⟩

/-- 屋根図式の指定対象での値は、元の始域からの実写像空間。 -/
lemma dgClosedVerdierRoofDiagram_obj (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    (dgClosedVerdierRoofDiagram A D P x y).obj (op s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y := rfl

/-- 屋根の射による作用は、指定された厳密細分射による実前合成。 -/
lemma dgClosedVerdierRoofDiagram_map (P : Set D) (x y : D)
    {s t : DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (dgClosedVerdierRoofDiagram A D P x y).map r.op =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D
        (q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left)
        (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) t.obj.left) (y := y) r.hom.left) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
