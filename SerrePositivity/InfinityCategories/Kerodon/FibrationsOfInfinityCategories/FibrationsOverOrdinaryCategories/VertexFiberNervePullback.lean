module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：通常の圏の nerve の関手で引き戻した射の頂点 fiber の同型。
方針：一般の引き戻しの fiber 同型に、nerve の頂点と関手の作用の一致を合成する。
規約：同型の包含後の計算則を明示し、頂点の表示の等式を隠さない。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、Definition 5.3.4.2（Tag 0255）、scaffold の底変換の fiber 条件。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：fiber の底の頂点の等式による輸送は元の全空間への包含を保つ。
方針：頂点の等式を代入して恒等射の計算に戻す。
規約：充填性は要求しない。
使われ方：Kerodon Definition 5.3.4.2（Tag 0255）、nerve の頂点の表示を揃える計算。 -/
lemma vertexFiberTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') :
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b' = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  subst b'
  rfl

/-- 概要：nerve の関手で引き戻した射の fiber は像の対象上の元の fiber と同型。
方針：一般の fiber の引き戻し同型の底の頂点を nerveMap の零単体の公式で同定する。
規約：H の充填性や忠実性は要求しない。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、scaffold の係数値ごとの底変換。 -/
noncomputable def vertexFiberNervePullbackIso
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p (nerveMap H)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (H.obj d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p (nerveMap H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) (nerveMap_app_mk₀ H d))

/-- 概要：nerve による底変換の fiber 同型を元へ含めると引き戻しの第一射影となる。
方針：頂点の輸送の包含後の計算と一般の fiber 同型の計算を使う。
規約：同型は fiber の選択を伴わない標準のもの。
使われ方：Kerodon Definition 5.3.4.2（Tag 0255）、底変換された scaffold の fiber 比較の計算。 -/
lemma vertexFiberNervePullbackIso_hom_ι
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    (vertexFiberNervePullbackIso p H d).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (H.obj d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd p (nerveMap H)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) ≫ pullback.fst p (nerveMap H) := by
  dsimp only [vertexFiberNervePullbackIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]
  exact nerveMap_app_mk₀ H d

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
