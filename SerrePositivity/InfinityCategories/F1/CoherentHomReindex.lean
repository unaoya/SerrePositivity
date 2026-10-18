module

public import SerrePositivity.InfinityCategories.F1.CoherentHomFaces

/-!
概要：豊穣 Hom の比較の座標射と添字写像の整合性。
方針：最後の頂点固定延長による path の像を関手にし、最大元の自然性を使う。
規約：二つの終点の表現の違いは等号による Hom の移送で明示する。
使われ方：Kerodon Construction 4.6.7.3、Remark 4.6.7.9、比較射の面・退化への自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の頂点を固定する path の添字変換は関手。
方針：部分集合の像と包含の保存を使う。
規約：変換後の始点は α(i)、終点は追加した最後の頂点。
使われ方：Kerodon Construction 4.6.7.3、比較の Hom 上の自然性。 -/
def pathLastReindexFunctor {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1))) ⥤
      Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1))) where
  obj := pathLastReindex α
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 概要：最大元で定める標準単体への射は path の添字変換に自然。
方針：標準単体の各頂点で最大元の添字変換則を使う。
規約：α は単射にも全射にも制限しない。
使われ方：Kerodon Construction 4.6.7.3、比較の全ての面と退化の整合性。 -/
lemma pathLastMaximumMap_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    nerveMap (pathLastReindexFunctor.{u} α i) ≫ pathLastMaximumMap (α.toOrderHom i) =
      pathLastMaximumMap i ≫ stdSimplex.map α := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  change ((pathLastMaximumMap (α.toOrderHom i)).app d
    ((nerveMap (pathLastReindexFunctor α i)).app d P)).down.toOrderHom k =
      α.toOrderHom (((pathLastMaximumMap i).app d P).down.toOrderHom k)
  rw [pathLastMaximumMap_apply, pathLastMaximumMap_apply]
  exact pathLastMaximum_reindex α (P.obj k)

/-- 概要：比較の Hom の非定値部分を端点の移送後に計算する。
方針：castSucc と最後の頂点の分岐を展開し、二端点の移送を打ち消す。
規約：値は最大元の射に沿って元の Hom 単体を評価したもの。
使われ方：Kerodon Construction 4.6.7.3、比較の Hom の自然性。 -/
lemma coherentHomComparisonHom_cast_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i : Fin (n + 1)) :
    coherentHomComparisonHom σ i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)) =
      pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ := by
  simp -implicitDefEqProofs +instances [coherentHomComparisonHom, coherentHomComparisonObj]

/-- 概要：比較の最後の自己 Hom の作用は端点の移送後に豊穣恒等に定値。
方針：二つの最後の頂点の分岐を展開して移送を打ち消す。
規約：始点と終点はともに Y に合わせる。
使われ方：Kerodon Construction 4.6.7.3、比較の終域の自然性。 -/
lemma coherentHomComparisonHom_last_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    coherentHomComparisonHom σ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)) =
      toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [coherentHomComparisonHom, coherentHomComparisonObj]

/-- 概要：比較の対象の作用は最後の頂点固定延長に整合する。
方針：最後の頂点とそれ以外で延長写像を計算する。
規約：同じ X と Y に対する異なる次数の対象の作用を比較する。
使われ方：Kerodon Construction 4.6.7.3、比較の豊穣関手の自然性の対象部分。 -/
lemma coherentHomComparisonObj_extend {C : Type v} (X Y : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom i) =
      coherentHomComparisonObj X Y i := by
  induction i using Fin.lastCases with
  | last =>
    rw [PinchedHom.extendOrderHom_last, coherentHomComparisonObj_last,
      coherentHomComparisonObj_last]
  | cast i =>
    rw [PinchedHom.extendOrderHom_castSucc, coherentHomComparisonObj_cast,
      coherentHomComparisonObj_cast]

end SerrePositivity.InfinityCategories
