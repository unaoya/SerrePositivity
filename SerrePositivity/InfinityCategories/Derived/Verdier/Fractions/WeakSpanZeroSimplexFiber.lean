module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanFixedSimplexCollapse
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)

/-- 概要：同じ元の終点を持つ span は、その零単体上の元の引き戻し fiber と実同型。
方針：元の零単体の初頂点等式で既存の同じ fiber 同型を輸送する。
規約：終点の値だけを等式で読み替え、span は変更しない。
使われ方：同じ元の Kan 単位の固定終点での回収。 -/
def weakSpanZeroSimplexFiberIso :
    fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≅
      vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)) :=
  eqToIso (congrArg (fun z => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x z)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex y).symm) ≪≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso i x (transportSimplexIndex (n := ⦋0⦌) y)

/-- 概要：同じ fiber 同型の包含後の射は、元の span を零単体上へ入れる実射そのもの。
方針：両引き戻し射影を計算し、元の fiber 輸送の包含式を使う。
規約：元の全単体上で厳密に一致する。
使われ方：元の全族の実 fiber 制限と単体圏単位の照合。 -/
theorem weakSpanZeroSimplexFiberIso_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso i x y).hom ≫
      vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift i x y := by
  let b := nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)
  let π := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x
  let r := transportSimplexFirstVertexMap B.obj
  let s := vertexFiberPullbackIso π r b
  have hs := congrArg (fun f => s.inv ≫ f) (vertexFiberPullbackIso_hom_ι π r b)
  change (s.inv ≫ s.hom) ≫ vertexFiberι π (r.app (Opposite.op ⦋0⦌) b) =
    (s.inv ≫ vertexFiberι (pullback.snd π r) b) ≫ pullback.fst π r at hs
  rw [s.inv_hom_id, Category.id_comp] at hs
  apply pullback.hom_ext
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso, Iso.trans_hom, eqToIso.hom,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso, Iso.symm_hom]
    simp only [Category.assoc]
    rw [show (vertexFiberPullbackIso π r b).inv ≫
      vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x) b ≫ pullback.fst π r =
        vertexFiberι π (r.app (Opposite.op ⦋0⦌) b) from (by simpa only [Category.assoc] using! hs.symm)]
    rw [show (markedSpanFamilyFiberIso B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x
      (r.app (Opposite.op ⦋0⦌) b)).hom ≫ vertexFiberι π _ =
        fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x _ from vertexFiberLift_ι _ _ _
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedFamily_projection i x (r.app (Opposite.op ⦋0⦌) b))]
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift, pullback.lift_fst]
    apply (cancel_mono (vertexFiberι (markedSpanSource B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)) x)).1
    simp only [Category.assoc, fixedMarkedSpanToFamily_inclusion]
    exact vertexFiberTransport_ι (markedSpanBoundary B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i))
      (congrArg (fun z => functorVertex (intervalMappingBoundary x z))
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex y).symm)
  · simp only [Category.assoc, vertexFiberι_comp, SSet.comp_const,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift, pullback.lift_snd]
    change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso i x y).hom ≫
      vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x) b ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x = _
    rw [vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanZeroSimplexFiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanZeroSimplexFiberIso_inclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanZeroSimplexFiberIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanZeroSimplexFiberIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso._proof_2
