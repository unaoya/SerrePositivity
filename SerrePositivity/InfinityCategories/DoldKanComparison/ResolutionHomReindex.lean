module

public import SerrePositivity.InfinityCategories.DoldKanComparison.ResolutionPathPushforward

/-!
# pinched 次数の変更に対する解像の Hom 評価の自然性

概要：pinched 単体の引き戻しの評価は、旗を押し出して元の単体を評価した値に一致する。
方針：豊穣関手の前合成と端点の移送を分離し、Path の像の一致を適用する。
規約：旗の次数と pinched 次数を区別する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の解像を介した写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

private lemma normalizedHom_transport {C : Type w} [EnrichedCategory SSet.{u} C]
    (F : EnrichedFunctor SSet C (ClosedCategory R D)) {a b a' b' : C}
    (ha : a = a') (hb : b = b') {x y : ClosedCategory R D}
    (hx : F.obj a' = x) (hy : F.obj b' = y) :
    F.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg F.obj ha).trans hx) ((congrArg F.obj hb).trans hy)) =
      eqToHom (congrArg₂ (fun a b : C ↦ a ⟶[SSet] b) ha hb) ≫
        F.map a' b' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hy) := by
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp]

/-- 概要：pinched 単体の引き戻しでの旗の評価は旗を押し出した評価に等しい。
方針：豊穣 Hom の前合成の式を端点の等式で正規化し、Path の像の計算を使う。
規約：面と退化を含む任意の pinched 次数の変更を扱う。
使われ方：Kerodon 2.5.9 の補助解像についての余単体的な比較。 -/
lemma resolutionHomValue_reindex {x y : ClosedCategory R D} {m n d : ℕ}
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌)
    (β : ⦋m⦌ ⟶ ⦋n⦌) (F : CoherentResolutionFlag m d) :
    resolutionHomValue ((coherentPinchedHom (R := R) (D := D) x y).map β.op s) F =
      resolutionHomValue s (F.pushforward β.toOrderHom) := by
  let a : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (PinchedHom.extendOrderHom β.toOrderHom F.start.castSucc))
  let b : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (PinchedHom.extendOrderHom β.toOrderHom (Fin.last (m + 1))))
  let a' : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (β.toOrderHom F.start).castSucc)
  let b' : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (Fin.last (n + 1)))
  have ha : a = a' := congrArg (fun i ↦ SimplicialThickening.mk (ULift.up i))
    (PinchedHom.extendOrderHom_castSucc β.toOrderHom F.start)
  have hb : b = b' := congrArg (fun i ↦ SimplicialThickening.mk (ULift.up i))
    (PinchedHom.extendOrderHom_last β.toOrderHom)
  have h := normalizedHom_transport s.val ha hb
    (coherentPinched_source_obj s (β.toOrderHom F.start)) (coherentPinched_target_obj s)
  have he : thickeningExtendHom β F.start.castSucc (Fin.last (m + 1)) ≫
      eqToHom (congrArg₂ (fun a b : SimplicialThickening (ULift.{u} (Fin (n + 2))) ↦
        a ⟶[SSet] b) ha hb) = nerveMap (pathLastReindexFunctor β F.start) :=
    thickeningExtend_map_cast_last β F.start
  have hmap : thickeningExtendHom β F.start.castSucc (Fin.last (m + 1)) ≫
      s.val.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        ((congrArg s.val.obj ha).trans (coherentPinched_source_obj s (β.toOrderHom F.start)))
        ((congrArg s.val.obj hb).trans (coherentPinched_target_obj s))) =
      nerveMap (pathLastReindexFunctor β F.start) ≫
        s.val.map a' b' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentPinched_source_obj s (β.toOrderHom F.start))
          (coherentPinched_target_obj s)) := by
    rw [h, ← Category.assoc, he]
  change ((thickeningExtendHom β F.start.castSucc (Fin.last (m + 1))) ≫
    s.val.map a b ≫ eqToHom _).app (Opposite.op ⦋d⦌) (resolutionFlagPathFunctor F) = _
  rw [hmap]
  change (s.val.map a' b' ≫ eqToHom _).app (Opposite.op ⦋d⦌)
    ((nerveMap (pathLastReindexFunctor β F.start)).app _ (resolutionFlagPathFunctor F)) = _
  rw [resolutionFlagPathFunctor_pushforward]
  rfl

/-- 概要：解像からの Hom 射は pinched 次数の引き戻しと旗の押し出しに整合する。
方針：全ての旗での評価の一致を単体集合の射の等式にする。
規約：固定した旗の次数についての自然性に加えて値域の次数の自然性を表す。
使われ方：HA 1.3.1.17 の解像を介した単体的な写像空間の比較。 -/
lemma resolutionHomMap_reindex {x y : ClosedCategory R D} {m n : ℕ}
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) (β : ⦋m⦌ ⟶ ⦋n⦌) :
    resolutionHomMap ((coherentPinchedHom (R := R) (D := D) x y).map β.op s) =
      coherentResolutionMap β.toOrderHom ≫ resolutionHomMap s := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro F
  exact resolutionHomValue_reindex s β F.down

end SerrePositivity.InfinityCategories.DoldKanComparison
