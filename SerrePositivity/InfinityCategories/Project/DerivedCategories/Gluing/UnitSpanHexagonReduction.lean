module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitSpanAlignedDiagonalTriangles
/-! # 実単位補正六角形から指定対角境界への消去

概要：実四補正道と実係数対角の六角形関係を、正本の指定三辺の充填へ移す。
方針：同じ三つの実合成三角形を使い、写像空間の可逆な辺の類を相殺する。
規約：六角形関係だけを補助入力とし、主比較の公開型へ仮定を追加しない。
使われ方：六片の単位面を消去して得る高次合成等式を主境界へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
lemma dgGluingUnitHexagon_cancel {E : Type u} [Category.{v} E] {a b c d e : E}
    (cf : a ≅ b) (k : c ≅ d) (dl : c ≅ e)
    (hl : b ⟶ c) (hf : b ⟶ d) (df : a ⟶ d) (cl : b ⟶ e) (bridge : a ⟶ e)
    (hfirst : cf.hom ≫ hf = df) (hlast : hl ≫ dl.hom = cl)
    (hbridge : cf.hom ≫ cl = bridge) (hhex : df ≫ k.inv ≫ dl.hom = bridge) :
    hl ≫ k.hom = hf := by
  apply (cancel_epi cf.hom).mp
  apply (cancel_mono (k.inv ≫ dl.hom)).mp
  calc
    _ = cf.hom ≫ cl := by
      simp only [Category.assoc, k.hom_inv_id_assoc]
      rw [hlast]
    _ = bridge := hbridge
    _ = df ≫ k.inv ≫ dl.hom := hhex.symm
    _ = _ := by rw [← hfirst]

variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingFirstCollarDiagonalSpanIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)

def dgGluingLastCapDiagonalSpanIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCapDiagonalSpanHomotopy R C D M X Y)

def dgGluingUnitCapCoefficientIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_actual_unit_hexagon
    (hhex : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y)) ≫
      (dgGluingUnitCapCoefficientIso R C D M X Y).inv ≫
        (dgGluingLastCapDiagonalSpanIso R C D M X Y).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarBridgeHomotopy R C D M X Y))) :
    ∃ V, (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary_filling_of_actual_coefficient_comp
    R C D M X Y
  exact dgGluingUnitHexagon_cancel
    (dgGluingFirstCollarDiagonalSpanIso R C D M X Y)
    (dgGluingUnitCapCoefficientIso R C D M X Y)
    (dgGluingLastCapDiagonalSpanIso R C D M X Y)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)))
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarBridgeHomotopy R C D M X Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitSpanAlignedDiagonalTriangle_homMk_comp R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitSpanAlignedDiagonalTriangle_homMk_comp R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarCompositionTriangle_homMk_comp R C D M X Y) hhex
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
