module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoslicePointTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoslicePostcompIdentity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InitialRelativeComparison

/-!
概要：指定全空間点からの標準輸送と元の coslice 射影を相対関手空間で比較する。
方針：両者を元の全空間点の coslice 上で比較し、恒等点評価の一致を使う。
規約：同型は底を厳密に保つ相対関手空間内に取る。
使われ方：全解錐を前合成して分類した retract の分裂等式を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (w : E _⦋0⦌)

/-- 概要：元の全空間の点を始点とする底の coslice 全体の輸送。
方針：同じ全空間点をその像上の fiber 点として標準輸送に渡す。
規約：始点 w を固定する。
使われ方：解錐の頂点からの共変 Hom 比較の逆向き。 -/
def cosliceVertexTransport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) w)) ⟶ E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coslicePointTransport p (p.app (Opposite.op ⦋0⦌) w)
    ⟨w, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]⟩).val

/-- 概要：指定全空間点の輸送は底の元の coslice 射影を保つ。
方針：底上の輸送の構成に付随する一致条件を使う。
規約：底の射影は元の指定点の像のもの。
使われ方：全解の輸送を同じ底上の比較に束ねる。 -/
lemma cosliceVertexTransport_projection :
    cosliceVertexTransport p w ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) w)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coslicePointTransport p (p.app (Opposite.op ⦋0⦌) w)
    ⟨w, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]⟩).property

/-- 概要：指定全空間点の輸送は恒等錐を元の同じ点へ送る。
方針：fiber 点の輸送の恒等点公式を使う。
規約：同型までではなく頂点の等式。
使われ方：始対象での二つの持ち上げの照合。 -/
lemma cosliceVertexTransport_identity :
    (cosliceVertexTransport p w).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (p.app (Opposite.op ⦋0⦌) w)) = w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coslicePointTransport_identity p _ _

/-- 概要：全空間の coslice 射影と底での標準輸送の引き戻しは相対関手空間で同型。
方針：元の恒等錐を始対象として、両持ち上げの同じ全空間点での一致を使う。
規約：底の全図式と元の全空間点を保持する。
使われ方：解錐による比較の合成が恒等になることの幾何的な証拠。 -/
def cosliceVertexTransportComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm w) ≫ p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm w)) rfl)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm w) ≫ p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp (SSet.yonedaEquiv.symm w) p
          (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) w))
          (SSet.yonedaEquiv_symm_comp w p) ≫ cosliceVertexTransport p w)
        (by rw [Category.assoc, cosliceVertexTransport_projection,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection])) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeFunctorIso_of_initial_evaluation_eq p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone w)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex w)
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coslicePostcomp_identity,
    cosliceVertexTransport_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
