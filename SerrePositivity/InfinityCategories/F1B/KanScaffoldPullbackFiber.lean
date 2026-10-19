module

public import SerrePositivity.InfinityCategories.F1.FunctorFiber
public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：引き戻しの頂点 fiber と元の対応する頂点 fiber の同型。
方針：第一射影で写し、逆を元の fiber と定値の底の成分の組で作る。
規約：fibration 性や quasicategory 性を仮定しない。
使われ方：一般の cocartesian scaffold の底変換と fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection

/-- 概要：引き戻しの頂点上の fiber は元の像の頂点上の fiber と同型。
方針：fiber の普遍性と引き戻しの両射影を使って互いに逆な射を作る。
規約：第二射影の fiber を取り、同型の順方向は第一射影で誘導する。
使われ方：一般の scaffold の底変換の fiber 条件。 -/
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

/-- 概要：fiber の底の頂点の等式による輸送は元の全空間への包含を保つ。
方針：頂点の等式を代入して恒等射の計算に戻す。
規約：充填性は要求しない。
使われ方：Kerodon Definition 5.3.4.2、nerve の頂点の表示を揃える計算。 -/
lemma vertexFiberTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') :
    eqToHom (congrArg (vertexFiber p) h) ≫ vertexFiberι p b' = vertexFiberι p b := by
  subst b'
  rfl

/-- 概要：nerve の関手で引き戻した射の fiber は像の対象上の元の fiber と同型。
方針：一般の fiber の引き戻し同型の底の頂点を nerveMap の零単体の公式で同定する。
規約：H の充填性や忠実性は要求しない。
使われ方：Kerodon Remark 5.3.2.3、scaffold の係数値ごとの底変換。 -/
noncomputable def vertexFiberNervePullbackIso
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    vertexFiber (pullback.snd p (nerveMap H)) (nerveVertex d) ≅
      vertexFiber p (nerveVertex (H.obj d)) :=
  vertexFiberPullbackIso p (nerveMap H) (nerveVertex d) ≪≫
    eqToIso (congrArg (vertexFiber p) (nerveMap_app_mk₀ H d))

/-- 概要：nerve による底変換の fiber 同型を元へ含めると引き戻しの第一射影となる。
方針：頂点の輸送の包含後の計算と一般の fiber 同型の計算を使う。
規約：同型は fiber の選択を伴わない標準のもの。
使われ方：Kerodon Definition 5.3.4.2、底変換された scaffold の fiber 比較の計算。 -/
lemma vertexFiberNervePullbackIso_hom_ι
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    (vertexFiberNervePullbackIso p H d).hom ≫ vertexFiberι p (nerveVertex (H.obj d)) =
      vertexFiberι (pullback.snd p (nerveMap H)) (nerveVertex d) ≫ pullback.fst p (nerveMap H) := by
  dsimp only [vertexFiberNervePullbackIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι, vertexFiberPullbackIso_hom_ι]
  exact nerveMap_app_mk₀ H d

end SerrePositivity.InfinityCategories.KanSection
