module

public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：引き戻しの頂点 fiber と元の対応する頂点 fiber の同型。
方針：第一射影で写し、逆を元の fiber と定値の底の成分の組で作る。
規約：fibration 性や quasicategory 性を仮定しない。
使われ方：Kerodon Remark 5.6.2.5、Example 5.6.2.9、unstraightening の fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：引き戻しの頂点上の fiber は元の像の頂点上の fiber と同型。
方針：fiber の普遍性と引き戻しの両射影を使って互いに逆な射を作る。
規約：第二射影の fiber を取り、同型の順方向は第一射影で誘導する。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の fiber を pointed space の fiber に移す。 -/
noncomputable def vertexFiberPullbackIso {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : vertexFiber (pullback.snd p f) b ≅
      vertexFiber p (f.app (Opposite.op ⦋0⦌) b) := by
  let q := pullback.snd p f
  let ι := vertexFiberι q b
  let ι' := vertexFiberι p (f.app (Opposite.op ⦋0⦌) b)
  have hh : (ι ≫ pullback.fst p f) ≫ p = SSet.const (f.app (Opposite.op ⦋0⦌) b) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (ι ≫ q) ≫ f = _
    rw [vertexFiberι_comp, SSet.const_comp]
  let H := vertexFiberLift p (f.app (Opposite.op ⦋0⦌) b) (ι ≫ pullback.fst p f) hh
  have hw : ι' ≫ p = (SSet.const b) ≫ f := by
    rw [vertexFiberι_comp, SSet.const_comp]
  let L := pullback.lift ι' (SSet.const b) hw
  have hL : L ≫ q = SSet.const b := pullback.lift_snd _ _ _
  let V := vertexFiberLift q b L hL
  have hH : H ≫ ι' = ι ≫ pullback.fst p f := vertexFiberLift_ι _ _ _ _
  have hV : V ≫ ι = L := vertexFiberLift_ι _ _ _ _
  refine { hom := H, inv := V, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply vertexFiber_hom_ext q b
    change (H ≫ V) ≫ ι = (𝟙 _) ≫ ι
    rw [Category.assoc, hV, Category.id_comp]
    apply pullback.hom_ext
    · change H ≫ L ≫ pullback.fst p f = ι ≫ pullback.fst p f
      rw [show L ≫ pullback.fst p f = ι' from pullback.lift_fst _ _ _, hH]
    · change H ≫ L ≫ q = ι ≫ q
      rw [hL, SSet.comp_const, vertexFiberι_comp]
  · apply vertexFiber_hom_ext p (f.app (Opposite.op ⦋0⦌) b)
    change (V ≫ H) ≫ ι' = (𝟙 _) ≫ ι'
    rw [Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact pullback.lift_fst _ _ _

/-- 概要：fiber の同型の順方向を元へ含めると第一射影になる。
方針：同型の定義の fiber への持ち上げを計算する。
規約：fiber の底の頂点は f の零次成分で写す。
使われ方：Kerodon Example 5.6.2.9、fiber 比較の自然性。 -/
lemma vertexFiberPullbackIso_hom_ι {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : (vertexFiberPullbackIso p f b).hom ≫
      vertexFiberι p (f.app (Opposite.op ⦋0⦌) b) =
        vertexFiberι (pullback.snd p f) b ≫ pullback.fst p f := rfl

end SerrePositivity.InfinityCategories
