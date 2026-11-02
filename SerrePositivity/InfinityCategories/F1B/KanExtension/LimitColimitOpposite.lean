module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanShapeCommaProjection
public import SerrePositivity.InfinityCategories.Core.ConeOpposite
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.ColimitReindex
public import SerrePositivity.InfinityCategories.F1.SquareDuality

/-!
概要：局所 Kan 図式の余極限と反転後の局所極限の存在を比較する。
方針：slice の反転同型で普遍錐を移し、局所添字の同型に沿って制限する。
規約：quasicategory 性を仮定しない存在条件の比較。
使われ方：左 Kan 拡張の存在定理を右側へ双対化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：図式の極限の存在は反転した図式の余極限の存在と同値。
方針：slice の反転同型を頂点に適用し、終対象と始対象の反転を使う。
規約：図式と標的は任意。
使われ方：点ごとの極限・余極限の存在の双対化。 -/
lemma kanHasLimit_iff_hasColimit_op {A D : SSet.{u}} (p : A ⟶ D) :
    HasLimit p ↔ HasColimit (SSet.opFunctor.map p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.reverseCocone, (isLimitCone_iff_reverseCocone c).1 hc⟩
  · rintro ⟨d, hd⟩
    let x := (sliceOverOpIso p).inv.app (Opposite.op ⦋0⦌) d
    let c : JoinCone p := SSet.opObjEquiv x
    refine ⟨c, ?_⟩
    change IsTerminalVertex (X := sliceOver p) c
    apply (isTerminalVertex_iff_isInitialVertex_op (X := sliceOver p) c).2
    exact hd.map_of_isIso (sliceOverOpIso p).inv

/-- 概要：同型な添字への制限は極限の存在を保ち反映する。
方針：slice の制限同型を頂点へ適用する。
規約：標的の充填性は不要。
使われ方：反転した標準局所図式の添字の正規化。 -/
lemma kanHasLimit_iff_restrict_of_isIso {A B D : SSet.{u}}
    (p : B ⟶ D) (f : A ⟶ B) [IsIso f] :
    HasLimit p ↔ HasLimit (f ≫ p) := by
  have := sliceOverRestrict_isIso p f
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(sliceOverRestrict p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (sliceOverRestrict p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (sliceOverRestrict p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (sliceOverRestrict p f))⟩

/-- 概要：同型な添字への制限は余極限の存在を保ち反映する。
方針：coslice の制限同型とその逆で始対象を写す。
規約：標的の充填性は不要。
使われ方：二重反転した図式の添字を戻す。 -/
lemma kanHasColimit_iff_restrict_of_isIso {A B D : SSet.{u}}
    (p : B ⟶ D) (f : A ⟶ B) [IsIso f] :
    HasColimit p ↔ HasColimit (f ≫ p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(sliceUnderRestrict p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (sliceUnderRestrict p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (sliceUnderRestrict p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (sliceUnderRestrict p f))⟩

/-- 概要：標的の同型への後合成は余極限の存在を保ち反映する。
方針：後合成による coslice の同型を使う。
規約：同型の指定以外に仮定を置かない。
使われ方：二重反転した図式の標的を戻す。 -/
lemma kanHasColimit_iff_postcomp_of_isIso {A D E : SSet.{u}}
    (p : A ⟶ D) (f : D ⟶ E) [IsIso f] :
    HasColimit p ↔ HasColimit (p ≫ f) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(sliceUnderPostcomp p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (sliceUnderPostcomp p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (sliceUnderPostcomp p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (sliceUnderPostcomp p f))⟩

/-- 概要：余極限の存在は反転した図式の極限の存在と同値。
方針：極限から余極限への反転をもう一度適用し、二重反転を同型で消去する。
規約：quasicategory 性は不要。
使われ方：左 Kan の局所存在条件を右側へ渡す。 -/
lemma kanHasColimit_iff_hasLimit_op {A D : SSet.{u}} (p : A ⟶ D) :
    HasColimit p ↔ HasLimit (SSet.opFunctor.map p) := by
  have h := kanHasColimit_iff_postcomp_of_isIso
    (SSet.opFunctor.map (SSet.opFunctor.map p)) (SSet.opFunctorCompOpFunctorIso.app D).hom
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality p
  change SSet.opFunctor.map (SSet.opFunctor.map p) ≫
    (SSet.opFunctorCompOpFunctorIso.app D).hom =
      (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ p at hn
  rw [hn] at h
  exact ((kanHasColimit_iff_restrict_of_isIso p
    (SSet.opFunctorCompOpFunctorIso.app A).hom).trans h.symm).trans
      (kanHasLimit_iff_hasColimit_op (SSet.opFunctor.map p)).symm

/-- 概要：左 Kan の局所余極限の存在は反転した右 Kan の局所極限の存在と同値。
方針：局所添字の反転同型が保つ図式を計算して極限の存在を移す。
規約：関手と三つの単体集合は任意。
使われ方：左の存在定理の双対化の入力。 -/
lemma kanLocalColimit_iff_oppositeLocalLimit {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    HasColimit (leftKanDiagram δ F₀ c) ↔
      HasLimit (rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opObjEquiv.symm c)) := by
  have h := kanHasLimit_iff_restrict_of_isIso
    (rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opObjEquiv.symm c)) (kanLeftKanShapeOpIso δ c).hom
  have hd : (kanLeftKanShapeOpIso δ c).hom ≫
      rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opObjEquiv.symm c) = SSet.opFunctor.map (leftKanDiagram δ F₀ c) := by
    dsimp only [rightKanDiagram, leftKanDiagram]
    rw [← Category.assoc, kanLeftKanShapeOpIso_projection, CategoryTheory.Functor.map_comp]
  rw [hd] at h
  exact (kanHasColimit_iff_hasLimit_op (leftKanDiagram δ F₀ c)).trans h.symm

end SerrePositivity.InfinityCategories.F1B
