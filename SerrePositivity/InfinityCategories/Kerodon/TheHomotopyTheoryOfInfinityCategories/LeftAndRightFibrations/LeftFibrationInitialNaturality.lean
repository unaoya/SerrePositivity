module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialSpan

/-! # 始対象からの比較 span の自然性

概要：同じ底上の関手は、始点を固定した二つの比較 span を可換に結ぶ。
方針：coslice の後合成を底の頂点 fiber へ制限し、表示変更を含めて二射影を比較する。
規約：空間の射の段階では充填性も始対象性も不要。使われ方：余錐制限と Hom 比較の両立。

対応節は Kerodon 4.2（Tag 014H）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：同じ底上の関手が保つ二つの始点の、底の点図式は等しい。
方針：Yoneda の自然性と底への合成の可換性を使う。
規約：始点の等号を明示する。使われ方：比較 span の底側の輸送。 -/
lemma leftFibrationInitialBaseDiagram_eq {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (c : E _⦋0⦌) (d : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) c = d) :
    SSet.yonedaEquiv.symm c ≫ p = SSet.yonedaEquiv.symm d ≫ q := by
  rw [← hf, ← Category.assoc, SSet.yonedaEquiv_symm_comp, hd]

/-- 概要：固定図式の等号による fiber の輸送は包含と可換。
方針：等号の帰納法で恒等射の場合に戻す。
規約：終点の頂点は固定。使われ方：比較 span の底側の正方形。 -/
lemma stableCosliceFiberChange_ι {K B : SSet.{u}} {a b : K ⟶ B}
    (h : a = b) (y : B _⦋0⦌) :
    eqToHom (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y) h) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b) y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) y ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) := by
  subst b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：底を保ち始点を指定の像へ送る関手は比較の中間空間に射を誘導する。
方針：始点下の coslice の後合成と表示変更を同じ底の fiber へ制限する。
規約：始点は始対象でなくてもよい。使われ方：図式制限による比較 span の写像。 -/
def leftFibrationInitialTotalMap {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (c : E _⦋0⦌) (d : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) c = d) (y : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p c y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal q d y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp (SSet.yonedaEquiv.symm c) f
    (SSet.yonedaEquiv.symm d) ((SSet.yonedaEquiv_symm_comp c f).trans
      (congrArg SSet.yonedaEquiv.symm hd))) (by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection, Category.assoc, hf]) y

/-- 概要：中間空間の関手による写像は終点評価と可換。
方針：fiber の包含後に coslice の後合成の射影を計算する。
規約：底への射と始点の等号は任意。使われ方：π₀ の比較の自然性の一辺。 -/
lemma leftFibrationInitialTotalMap_evaluation {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (c : E _⦋0⦌) (d : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) c = d) (y : B _⦋0⦌) :
    leftFibrationInitialTotalMap p q f hf c d hd y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q d y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p c y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
  simp only [leftFibrationInitialTotalMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection]
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

/-- 概要：中間空間の関手による写像は底側への射影と図式表示の輸送の下で可換。
方針：包含後に二段階の coslice 後合成を一段階へまとめる。
規約：底側は元の始点の像の図式に揃える。使われ方：π₀ の比較の自然性の第二の辺。 -/
lemma leftFibrationInitialTotalMap_projection {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (c : E _⦋0⦌) (d : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) c = d) (y : B _⦋0⦌) :
    leftFibrationInitialTotalMap p q f hf c d hd y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q d y ≫
      eqToHom (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y)
        (leftFibrationInitialBaseDiagram_eq p q f hf c d hd).symm) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection p c y := by
  subst p
  have hf : f ≫ q = f ≫ q := rfl
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ (f ≫ q))) y
  rw [Category.assoc, Category.assoc, stableCosliceFiberChange_ι
    (leftFibrationInitialBaseDiagram_eq (f ≫ q) q f hf c d hd).symm y]
  dsimp only [leftFibrationInitialTotalMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  simp only [Category.assoc]
  apply congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ (f ≫ q)) y ≫ t)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_comp (SSet.yonedaEquiv.symm c) f
    (SSet.yonedaEquiv.symm d) ((SSet.yonedaEquiv_symm_comp c f).trans
      (congrArg SSet.yonedaEquiv.symm hd)) q (SSet.yonedaEquiv.symm c ≫ (f ≫ q))
      (leftFibrationInitialBaseDiagram_eq (f ≫ q) q f hf c d hd).symm
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp, hf, eqToHom_refl, Category.comp_id,
    Category.assoc] using hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
