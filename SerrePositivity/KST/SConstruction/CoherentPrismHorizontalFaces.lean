module
public import SerrePositivity.InfinityCategories.Kan.CoherentStringPrismChains
public import SerrePositivity.KST.SConstruction.CoherentOrdinaryPrismSlices

/-! # 上下の合成列の水平面は元の全入力列
概要：縦辺を加えた上下の合成列の外側面を、固定時刻の元の入力列へ厳密に同定する。
方針：外側面と入力射影・時刻の合成を先に計算し、元の全射列を回収する。
規約：長さ零の入力も含め、元の面作用を保つ。
使われ方：上下の元の豊穣作用を strict な水平図式と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 下側の水平面の入力射影は元の恒等再添字。 -/
lemma coherentLowerStringFace_index (n : ℕ) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ coherentLowerStringIndex n = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (coherentLowerStringIndex n).toOrderHom ((Fin.last (n + 1)).succAbove i) = i
  simp [Fin.succAbove_last, _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringIndex]

/-- 下側の水平面の時刻は元の定数零。 -/
lemma coherentLowerStringFace_time (n : ℕ) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ coherentLowerStringTime n =
      SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (coherentLowerStringTime n).toOrderHom ((Fin.last (n + 1)).succAbove i) = 0
  simp [Fin.succAbove_last, _root_.SerrePositivity.InfinityCategories.Kan.coherentLowerStringTime]

/-- 上側の水平面の入力射影は元の恒等再添字。 -/
lemma coherentUpperStringFace_index (n : ℕ) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ coherentUpperStringIndex n = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (coherentUpperStringIndex n).toOrderHom ((0 : Fin (n + 2)).succAbove i) = i
  simp [_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringIndex]

/-- 上側の水平面の時刻は元の定数一。 -/
lemma coherentUpperStringFace_time (n : ℕ) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ coherentUpperStringTime n =
      SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (coherentUpperStringTime n).toOrderHom ((0 : Fin (n + 2)).succAbove i) = 1
  simp [_root_.SerrePositivity.InfinityCategories.Kan.coherentUpperStringTime]

/-- 下側の水平面は、時刻零に含めた元の全入力列そのもの。 -/
lemma coherentLowerPrismString_horizontalFace {I : Type u} [SmallCategory I]
    {x y : I} {f : x ⟶ y} (s : CoherentArrowString f) :
    (nerve (I × ULift.{u} (Fin 2))).map (SimplexCategory.δ (Fin.last (s.length + 1))).op
      (coherentLowerPrismString s).chain =
      (nerveMap (coherentPrismSliceFunctor I (ULift.up 0))).app (Opposite.op ⦋s.length⦌)
        s.chain := by
  change (nerve (I × ULift.{u} (Fin 2))).map _
    (coherentStringPrismChain s (coherentLowerStringIndex _) (coherentLowerStringTime _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex, coherentLowerStringFace_index,
    coherentLowerStringFace_time]
  rfl

/-- 上側の水平面は、時刻一に含めた元の全入力列そのもの。 -/
lemma coherentUpperPrismString_horizontalFace {I : Type u} [SmallCategory I]
    {x y : I} {f : x ⟶ y} (s : CoherentArrowString f) :
    (nerve (I × ULift.{u} (Fin 2))).map (SimplexCategory.δ (0 : Fin (s.length + 2))).op
      (coherentUpperPrismString s).chain =
      (nerveMap (coherentPrismSliceFunctor I (ULift.up 1))).app (Opposite.op ⦋s.length⦌)
        s.chain := by
  change (nerve (I × ULift.{u} (Fin 2))).map _
    (coherentStringPrismChain s (coherentUpperStringIndex _) (coherentUpperStringTime _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kan.coherentStringPrismChain_reindex, coherentUpperStringFace_index,
    coherentUpperStringFace_time]
  rfl

/-- 下側の元の豊穣単体の水平面は、固定時刻の全入力図式の同じ単体そのもの。 -/
lemma coherentLowerPrismString_rawHorizontalCell {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} {f : x ⟶ y} (s : CoherentArrowString f) :
    (SimplicialThickening.functor (SimplexCategory.δ (Fin.last (s.length + 1))).toOrderHom.uliftMap).comp SSet
      (Q.app _ (ULift.up (coherentLowerPrismString s).chain)) =
      ((SSet.uliftFunctor.{v, u}).map
        (nerveMap (coherentPrismSliceFunctor I (ULift.up 0))) ≫ Q).app
          (Opposite.op ⦋s.length⦌) (ULift.up s.chain) := by
  have h := congrArg (fun a => a (ULift.up (coherentLowerPrismString s).chain))
    (Q.naturality (SimplexCategory.δ (Fin.last (s.length + 1))).op)
  change Q.app _ (ULift.up ((nerve (I × ULift.{u} (Fin 2))).map
    (SimplexCategory.δ (Fin.last (s.length + 1))).op (coherentLowerPrismString s).chain)) =
    (SimplicialNerve C).map _ (Q.app _ (ULift.up (coherentLowerPrismString s).chain)) at h
  rw [coherentLowerPrismString_horizontalFace] at h
  exact h.symm

/-- 上側の元の豊穣単体の水平面は、固定時刻の全入力図式の同じ単体そのもの。 -/
lemma coherentUpperPrismString_rawHorizontalCell {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} {f : x ⟶ y} (s : CoherentArrowString f) :
    (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin (s.length + 2))).toOrderHom.uliftMap).comp SSet
      (Q.app _ (ULift.up (coherentUpperPrismString s).chain)) =
      ((SSet.uliftFunctor.{v, u}).map
        (nerveMap (coherentPrismSliceFunctor I (ULift.up 1))) ≫ Q).app
          (Opposite.op ⦋s.length⦌) (ULift.up s.chain) := by
  have h := congrArg (fun a => a (ULift.up (coherentUpperPrismString s).chain))
    (Q.naturality (SimplexCategory.δ (0 : Fin (s.length + 2))).op)
  change Q.app _ (ULift.up ((nerve (I × ULift.{u} (Fin 2))).map
    (SimplexCategory.δ (0 : Fin (s.length + 2))).op (coherentUpperPrismString s).chain)) =
    (SimplicialNerve C).map _ (Q.app _ (ULift.up (coherentUpperPrismString s).chain)) at h
  rw [coherentUpperPrismString_horizontalFace] at h
  exact h.symm

end SerrePositivity.KST.SConstruction
