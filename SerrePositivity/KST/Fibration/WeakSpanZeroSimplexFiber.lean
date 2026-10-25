module
public import SerrePositivity.KST.Fibration.WeakSpanFixedSimplexCollapse
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback

/-!
概要：元の固定終点を持つ span と零単体上の引き戻し fiber の座標を厳密に照合する。
方針：既存の span fiber 同型と引き戻し fiber 同型を、元の零単体の頂点公式で移す。
規約：元の全族包含と零単体を保持する。
使われ方：K-B-S の全 fiber 回収を文字通り元の終点の座標へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B) (x y : B.obj _⦋0⦌)

/-- 概要：同じ元の終点を持つ span は、その零単体上の元の引き戻し fiber と実同型。
方針：元の零単体の初頂点等式で既存の同じ fiber 同型を輸送する。
規約：終点の値だけを等式で読み替え、span は変更しない。
使われ方：同じ元の Kan 単位の固定終点での回収。 -/
def weakSpanZeroSimplexFiberIso :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ≅
      vertexFiber (weakSpanSimplexProjection i x)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)) :=
  eqToIso (congrArg (fun z => fixedMarkedSpans B.obj (weakEquivalences i) x z)
    (transportSimplexFirstVertexMap_zeroIndex y).symm) ≪≫
      weakSpanSimplexFiberIso i x (transportSimplexIndex (n := ⦋0⦌) y)

/-- 概要：同じ fiber 同型の包含後の射は、元の span を零単体上へ入れる実射そのもの。
方針：両引き戻し射影を計算し、元の fiber 輸送の包含式を使う。
規約：元の全単体上で厳密に一致する。
使われ方：元の全族の実 fiber 制限と単体圏単位の照合。 -/
theorem weakSpanZeroSimplexFiberIso_inclusion :
    (weakSpanZeroSimplexFiberIso i x y).hom ≫
      vertexFiberι (weakSpanSimplexProjection i x)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)) =
      weakSpanFixedZeroSimplexLift i x y := by
  let b := nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)
  let π := markedSpanFamilyProjection B.obj (weakEquivalences i) x
  let r := transportSimplexFirstVertexMap B.obj
  let s := vertexFiberPullbackIso π r b
  have hs := congrArg (fun f => s.inv ≫ f) (vertexFiberPullbackIso_hom_ι π r b)
  change (s.inv ≫ s.hom) ≫ vertexFiberι π (r.app (Opposite.op ⦋0⦌) b) =
    (s.inv ≫ vertexFiberι (pullback.snd π r) b) ≫ pullback.fst π r at hs
  rw [s.inv_hom_id, Category.id_comp] at hs
  apply pullback.hom_ext
  · dsimp only [weakSpanZeroSimplexFiberIso, Iso.trans_hom, eqToIso.hom,
      weakSpanSimplexFiberIso, Iso.symm_hom]
    simp only [Category.assoc]
    rw [show (vertexFiberPullbackIso π r b).inv ≫
      vertexFiberι (weakSpanSimplexProjection i x) b ≫ pullback.fst π r =
        vertexFiberι π (r.app (Opposite.op ⦋0⦌) b) from (by simpa only [Category.assoc] using! hs.symm)]
    rw [show (markedSpanFamilyFiberIso B.obj (weakEquivalences i) x
      (r.app (Opposite.op ⦋0⦌) b)).hom ≫ vertexFiberι π _ =
        fixedMarkedSpanToFamily B.obj (weakEquivalences i) x _ from vertexFiberLift_ι _ _ _
          (weakSpanFixedFamily_projection i x (r.app (Opposite.op ⦋0⦌) b))]
    rw [weakSpanFixedZeroSimplexLift, pullback.lift_fst]
    apply (cancel_mono (vertexFiberι (markedSpanSource B.obj (weakEquivalences i)) x)).1
    simp only [Category.assoc, fixedMarkedSpanToFamily_inclusion]
    exact vertexFiberTransport_ι (markedSpanBoundary B.obj (weakEquivalences i))
      (congrArg (fun z => functorVertex (intervalMappingBoundary x z))
        (transportSimplexFirstVertexMap_zeroIndex y).symm)
  · simp only [Category.assoc, vertexFiberι_comp, SSet.comp_const,
      weakSpanFixedZeroSimplexLift, pullback.lift_snd]
    change (weakSpanZeroSimplexFiberIso i x y).hom ≫
      vertexFiberι (weakSpanSimplexProjection i x) b ≫ weakSpanSimplexProjection i x = _
    rw [vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.KST.Fibration
