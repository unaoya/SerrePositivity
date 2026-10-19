module

public import SerrePositivity.InfinityCategories.F1B.KanJoinDiagonalOpposite
public import SerrePositivity.InfinityCategories.F1.RelativeJoin
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：relative join の反転同型と両包含の交換。
方針：反転による pullback の保存と、join の反転、区間付き対角の両立を合わせる。
規約：二つの係数の順序を交換し、区間の両端も交換する。
使われ方：任意の右指定変換の相対 join 表示を左側の比較から導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：区間付き係数の反転を通常の区間付き反転係数へ戻す同型。
方針：直積の反転と標準区間の反転同型を合成する。
規約：順方向は反転した prism から通常の区間へ。
使われ方：relative join の係数の比較。 -/
def kanPrismOppositeIso (S : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ S).op ≅ (Δ[1] : SSet.{u}) ⊗ S.op :=
  (opTensorIso Δ[1] S).symm ≪≫
    ((stdSimplex.opIso ⦋1⦌) ⊗ᵢ Iso.refl S.op)

/-- 概要：底の対角の反転は join と prism の反転同型で両立する。
方針：反転した対角の計算の前から prism の逆同型を消去する。
規約：pullback.map に渡す向きの可換性。
使われ方：relative join の反転同型の構成。 -/
lemma kanJoinDiagonal_opposite_square (S : SSet.{u}) :
    SSet.opFunctor.map (joinDiagonal S) ≫ (stableJoinReverseIso S S).hom =
      (kanPrismOppositeIso S).hom ≫ joinDiagonal S.op := by
  apply (cancel_epi (kanPrismOppositeIso S).inv).1
  rw [← Category.assoc, Iso.inv_hom_id_assoc]
  exact kanJoinDiagonal_reverse S

/-- 概要：relative join の反転は反転した二係数を交換した relative join と同型。
方針：pullback を反転で保存し、三つの比較同型から pullback の同型を作る。
規約：係数の射に単射性や充填性を仮定しない。
使われ方：右 Kan の写像円柱比較の双対化。 -/
def kanRelativeJoinOppositeIso {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (relativeJoin f g).op ≅ relativeJoin (SSet.opFunctor.map g) (SSet.opFunctor.map f) :=
  PreservesPullback.iso SSet.opFunctor (joinMap f g) (joinDiagonal S) ≪≫
    asIso (pullback.map (SSet.opFunctor.map (joinMap f g))
      (SSet.opFunctor.map (joinDiagonal S))
      (joinMap (SSet.opFunctor.map g) (SSet.opFunctor.map f)) (joinDiagonal S.op)
      (stableJoinReverseIso X Y).hom (kanPrismOppositeIso S).hom
      (stableJoinReverseIso S S).hom (stableJoinReverse_naturality f g)
      (kanJoinDiagonal_opposite_square S))

/-- 概要：relative join の反転同型は通常の join への射影と可換。
方針：pullback の保存の射影と pullback.map の第一成分を計算する。
規約：全単体での厳密な等式。
使われ方：反転した両包含と prism の比較。 -/
lemma kanRelativeJoinOppositeIso_fst {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (kanRelativeJoinOppositeIso f g).hom ≫
      pullback.fst (joinMap (SSet.opFunctor.map g) (SSet.opFunctor.map f))
        (joinDiagonal S.op) =
      SSet.opFunctor.map (pullback.fst (joinMap f g) (joinDiagonal S)) ≫
        (stableJoinReverseIso X Y).hom := by
  simp only [kanRelativeJoinOppositeIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.lift_fst, PreservesPullback.iso_hom_fst_assoc]

/-- 概要：relative join の反転同型は区間付き係数への射影と可換。
方針：pullback の保存と pullback.map の第二成分を計算する。
規約：区間は両端を交換する。
使われ方：反転した両包含と prism の係数の比較。 -/
lemma kanRelativeJoinOppositeIso_snd {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (kanRelativeJoinOppositeIso f g).hom ≫
      pullback.snd (joinMap (SSet.opFunctor.map g) (SSet.opFunctor.map f))
        (joinDiagonal S.op) =
      SSet.opFunctor.map (pullback.snd (joinMap f g) (joinDiagonal S)) ≫
        (kanPrismOppositeIso S).hom := by
  simp only [kanRelativeJoinOppositeIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.lift_snd, PreservesPullback.iso_hom_snd_assoc]

/-- 概要：prism の反転同型は二つの端点を交換する。
方針：各次数で反転した区間の定値単体を比較する。
規約：係数の反転は同じ次数の同値で読む。
使われ方：relative join の両端の交換。 -/
lemma kanPrismOppositeIso_endpoint (S : SSet.{u}) (i : Fin 2) :
    SSet.opFunctor.map (prismEndpoint i S) ≫ (kanPrismOppositeIso S).hom =
      prismEndpoint i.rev S.op := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    rfl
  · rfl

/-- 概要：反転した左包含は反対側の右包含に一致する。
方針：join の反転の左境界と、区間の端点交換を両射影で使う。
規約：左右の係数の順番も交換する。
使われ方：右相対 join 表示の端点の比較。 -/
lemma kanRelativeJoinOppositeIso_inl {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    SSet.opFunctor.map (relativeJoinInl f g) ≫ (kanRelativeJoinOppositeIso f g).hom =
      relativeJoinInr (SSet.opFunctor.map g) (SSet.opFunctor.map f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinOppositeIso_fst, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, relativeJoinInl_fst, stableJoinReverse_inl,
      relativeJoinInr_fst]
  · rw [Category.assoc, kanRelativeJoinOppositeIso_snd, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]
    simp only [relativeJoinInl, relativeJoinInr, pullback.lift_snd,
      CategoryTheory.Functor.map_comp, Category.assoc, kanPrismOppositeIso_endpoint]
    rfl

/-- 概要：反転した右包含は反対側の左包含に一致する。
方針：join の反転の右境界と、区間の端点交換を両射影で使う。
規約：全単体での厳密な等式。
使われ方：右相対 join 表示の指定自然変換の端点。 -/
lemma kanRelativeJoinOppositeIso_inr {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    SSet.opFunctor.map (relativeJoinInr f g) ≫ (kanRelativeJoinOppositeIso f g).hom =
      relativeJoinInl (SSet.opFunctor.map g) (SSet.opFunctor.map f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinOppositeIso_fst, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, relativeJoinInr_fst, stableJoinReverse_inr,
      relativeJoinInl_fst]
  · rw [Category.assoc, kanRelativeJoinOppositeIso_snd, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]
    simp only [relativeJoinInl, relativeJoinInr, pullback.lift_snd,
      CategoryTheory.Functor.map_comp, Category.assoc, kanPrismOppositeIso_endpoint]
    rfl

end SerrePositivity.InfinityCategories
