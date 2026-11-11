module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomNaturality

/-!
概要：三対象の合成 simplex の Hom の添字変換の座標。
方針：path の集合が同じなら最大座標も同じことを使い、端点の等号による移送を保つ。
規約：元の単体圏の射は面・退化の双方を含む。
使われ方：標準のパラメーター付き合成 prism の単体的な自然性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：path の部分集合が同じなら、終点の表示によらず切替前の最大座標は同じ。
方針：最大元を取る有限集合を同定する。
規約：二つの終点は同じでなくてもよい。
使われ方：添字変換後の Hom の端点の移送。 -/
lemma pathCutMaximum_congr_I {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j k : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j))
    (Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up k)) (h : P.I = Q.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast t P = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast t Q := by
    classical
    ext l
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast, Finset.mem_filter, Finset.mem_univ, true_and, h]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum
  simp only [hs]

/-- 概要：合成 simplex の対象の作用は最後の頂点固定延長と整合する。
方針：最後の頂点と元の頂点の二つの場合に分ける。
規約：二値ラベルも同じ添字写像で引き戻す。
使われ方：合成 simplex の面・退化の自然性の対象部分。 -/
lemma coherentCompositionObj_extend {C : Type v} (X Y Z : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (t : Fin (n + 1) →o Fin 2) (i : Fin (m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z (t.comp α.toOrderHom) i := by
  induction i using Fin.lastCases
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last]
  · rename_i i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.lastCases_castSucc, OrderHom.comp_coe,
      Function.comp_apply]

/-- 概要：合成 simplex の Hom の端点の等号を移送する計算則。
方針：二端点の等号を消去し、Hom の表示変更を比較する。
規約：標準の対象 A と B への最終的な正規化を含める。
使われ方：合成 simplex の自然性の各場合の共通部分。 -/
lemma coherentCompositionHom_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z A B : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    {i j i' j' : Fin (n + 2)} (hi : i = i') (hj : j = j')
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i' = A)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t j' = B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t) hi).trans hA)
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t) hj).trans hB)) =
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i' j' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  subst i'
  subst j'
  simp

/-- 概要：thickening の添字変換と端点の移送後の切替座標は元の座標の添字変換に一致する。
方針：path の部分集合の移送不変性と最大座標の自然性を使う。
規約：終点 j' は延長した終点を等号で表示し直したもの。
使われ方：標準合成 simplex の最初の豊穣射の自然性。 -/
lemma thickeningExtend_pathCutMaximumMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (m + 1)) (hi : t (α.toOrderHom i) = 0)
    (j : Fin (m + 2)) (j' : Fin (n + 2))
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j = j') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc j ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i) hj)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap (t.comp α.toOrderHom) hi j ≫ stdSimplex.map α := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  let Q := ((eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i) hj)).app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc j).app (Opposite.op ⦋d⦌) P)).obj k
  have hQ : Q.I = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReindex α (P.obj k)).I := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
      (congrArg (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i))
      (congrArg (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))) hj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc j).app (Opposite.op ⦋d⦌) P) k
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q = α.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum (t.comp α.toOrderHom) hi (P.obj k))
  exact (pathCutMaximum_congr_I t hi Q _ hQ).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_reindex α t hi (P.obj k))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
