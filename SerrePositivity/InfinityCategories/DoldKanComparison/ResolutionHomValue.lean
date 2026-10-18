module

public import SerrePositivity.InfinityCategories.DoldKanComparison.ResolutionPathPullback

/-!
# coherent pinched 単体の解像の旗での評価

概要：coherent pinched 単体の豊穣 Hom 写像を解像の各旗で評価し、固定した二対象の標準単体を得る。
方針：先頭面・最終頂点の条件から端点を同定し、native Path の旗を Hom 写像へ送る。
規約：各旗での値を定義する段階であり、全ての添字での自然性は別途証明する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の解像を介する反対側の合成のホモトピーの構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：coherent pinched 単体の最後以外の各対象は固定した始対象である。
方針：先頭面の等式を各対象で評価する。
規約：対象の等式は閉零射の圏で述べる。
使われ方：Kerodon 2.5.9 の解像の旗での評価の始域の同定。 -/
lemma coherentPinched_source_obj {x y : ClosedCategory R D} {n : ℕ}
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) (i : Fin (n + 1)) :
    s.val.obj (.mk (ULift.up i.castSucc)) = x :=
  congrArg (fun F : doldKanCoherentNerve (R := R) (D := D) _⦋n⦌ ↦
    F.obj (.mk (ULift.up i))) s.source

/-- 概要：coherent pinched 単体の最後の対象は固定した終対象である。
方針：最後の頂点の等式を唯一の対象で評価する。
規約：対象の等式は閉零射の圏で述べる。
使われ方：HA 1.3.1.17 の評価の終域の同定。 -/
lemma coherentPinched_target_obj {x y : ClosedCategory R D} {n : ℕ}
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    s.val.obj (.mk (ULift.up (Fin.last (n + 1)))) = y :=
  congrArg (fun F : doldKanCoherentNerve (R := R) (D := D) _⦋0⦌ ↦
    F.obj (.mk (ULift.up 0))) s.target

/-- 概要：coherent pinched 単体を解像の旗で評価して標準 Hom の単体を取る。
方針：旗を native Path の単体にし、豊穣 Hom 写像と端点の移送を順に適用する。
規約：端点の移送は既存の pinched 条件から得る。
使われ方：Kerodon 2.5.9 の解像上の写像との対応の各次数の値。 -/
def resolutionHomValue {x y : ClosedCategory R D} {n d : ℕ}
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌)
    (F : CoherentResolutionFlag n d) : StandardSimplex R (D := D) x y d :=
  (s.val.map (.mk (ULift.up F.start.castSucc)) (.mk (ULift.up (Fin.last (n + 1)))) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentPinched_source_obj s F.start) (coherentPinched_target_obj s))).app
        (Opposite.op ⦋d⦌) (resolutionFlagPathFunctor F)

/-- 概要：解像の旗を最大頂点の射で写すと、元の旗の最大元の単調写像になる。
方針：F1 の最大頂点の射の各頂点の計算と Path の最大元の一致を使う。
規約：追加した最終点は最大元から除く。
使われ方：HA 1.3.1.17 の逆向きの射の解像での評価。 -/
lemma pathLastMaximumMap_resolutionFlag {n d : ℕ} (F : CoherentResolutionFlag n d) :
    (pathLastMaximumMap F.start).app (Opposite.op ⦋d⦌) (resolutionFlagPathFunctor.{u} F) =
      ULift.up (SimplexCategory.mkHom ⟨F.maxAt, F.maxAt_monotone⟩) := by
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro t
  exact (pathLastMaximumMap_apply F.start _ t).trans (resolutionFlagPath_maximum F t)

/-- 概要：標準 Hom から作った coherent pinched 単体の旗での値は最大元での引き戻しである。
方針：F1 の豊穣 Hom の正規化を使い、旗の最大頂点の計算を米田の評価へ移す。
規約：全次数の全ての旗での厳密な等式。
使われ方：Kerodon 2.5.9 の逆向きの射と解像の射影の一致。 -/
lemma resolutionHomValue_standard {x y : ClosedCategory R D} {n d : ℕ}
    (σ : StandardSimplex R (D := D) x y n) (F : CoherentResolutionFlag n d) :
    resolutionHomValue (standardCoherentPinchedSimplex σ) F =
      standardPullback ⟨F.maxAt, F.maxAt_monotone⟩ σ := by
  change ((coherentHomComparisonHom (X := x) (Y := y) σ F.start.castSucc
    (Fin.last (n + 1))) ≫ eqToHom _).app (Opposite.op ⦋d⦌) (resolutionFlagPathFunctor F) = _
  rw [coherentHomComparisonHom_cast_last (X := x) (Y := y) σ F.start]
  let φ : (Δ[n] : SSet.{u}) ⟶ standardHomSpace (R := R) (D := D) x y := SSet.yonedaEquiv.symm σ
  change φ.app (Opposite.op ⦋d⦌)
    ((pathLastMaximumMap F.start).app _ (resolutionFlagPathFunctor F)) = _
  rw [pathLastMaximumMap_resolutionFlag]
  rfl

end SerrePositivity.InfinityCategories.DoldKanComparison
