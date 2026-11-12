module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：引き戻しの頂点 fiber と元の対応する頂点 fiber の同型。
方針：第一射影で写し、逆を元の fiber と定値の底の成分の組で作る。
規約：fibration 性や quasicategory 性を仮定しない。
使われ方：Kerodon Example 5.6.2.19（Tag 0272）、Example 5.6.2.9（Tag 026S）、unstraightening の fiber 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：引き戻しの頂点上の fiber は元の像の頂点上の fiber と同型。
方針：fiber の普遍性と引き戻しの両射影を使って互いに逆な射を作る。
規約：第二射影の fiber を取り、同型の順方向は第一射影で誘導する。
使われ方：Kerodon Example 5.6.2.19（Tag 0272）、unstraightening の fiber を pointed space の fiber に移す。 -/
noncomputable def vertexFiberPullbackIso {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p f) b ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (f.app (Opposite.op ⦋0⦌) b) := by
  let q := pullback.snd p f
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
  let ι' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (f.app (Opposite.op ⦋0⦌) b)
  have hh : (ι ≫ pullback.fst p f) ≫ p = SSet.const (f.app (Opposite.op ⦋0⦌) b) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (ι ≫ q) ≫ f = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (f.app (Opposite.op ⦋0⦌) b) (ι ≫ pullback.fst p f) hh
  have hw : ι' ≫ p = (SSet.const b) ≫ f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  let L := pullback.lift ι' (SSet.const b) hw
  have hL : L ≫ q = SSet.const b := pullback.lift_snd _ _ _
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b L hL
  have hH : H ≫ ι' = ι ≫ pullback.fst p f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hV : V ≫ ι = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine { hom := H, inv := V, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    change (H ≫ V) ≫ ι = (𝟙 _) ≫ ι
    rw [Category.assoc, hV, Category.id_comp]
    apply pullback.hom_ext
    · change H ≫ L ≫ pullback.fst p f = ι ≫ pullback.fst p f
      rw [show L ≫ pullback.fst p f = ι' from pullback.lift_fst _ _ _, hH]
    · change H ≫ L ≫ q = ι ≫ q
      rw [hL, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p (f.app (Opposite.op ⦋0⦌) b)
    change (V ≫ H) ≫ ι' = (𝟙 _) ≫ ι'
    rw [Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact pullback.lift_fst _ _ _

/-- 概要：fiber の同型の順方向を元へ含めると第一射影になる。
方針：同型の定義の fiber への持ち上げを計算する。
規約：fiber の底の頂点は f の零次成分で写す。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、fiber 比較の自然性。 -/
lemma vertexFiberPullbackIso_hom_ι {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : (vertexFiberPullbackIso p f b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (f.app (Opposite.op ⦋0⦌) b) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd p f) b ≫ pullback.fst p f := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
