module

public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramPiZero
public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramFrameComparison

/-!
# 元の定値図式からの射の零単体の錐の類

概要：Hovey §5.4 の π₀ 比較が元の同じ図式射を回収することを証明する。
方針：frame の augmentation で作った零単体を比較し、二つの同型を相殺する。
規約：元の射とその局所化像を保持する。
使われ方：一般 homotopy 極限の元の錐と導来 Hom の整合性。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：元の定値図式からの射を錐の零単体の連結成分へ送る（Hovey §5.4）。
方針：構成した図式 frame の augmentation を元の射へ前合成する。
規約：元の始域代数の cofibrancy は不要。
使われ方：局所化 Hom と元の錐の射の同定。 -/
def constantDiagramSourceClass {Y : (operad A).Algebra}
    {F : K ⥤ (operad A).Algebra} (f : (Functor.const K).obj Y ⟶ F) :
    SSet.π₀ ((constantDiagramSourceHom A K Y).obj F) :=
  SSet.mapπ₀ ((constantDiagramFrameHomIso A K Y).app F).hom
    (SSet.π₀.mk ((constantDiagramFrameComparison A K Y).app (SimplexCategory.mk 0) ≫ f))

/-- 概要：元の図式射の錐の類は局所化で同じ図式射になる（Hovey §5.4）。
方針：零単体の計算式と二つの比較同型の相殺を使う。
規約：π₀ 比較は元の定値図式からの Hom を値に取る。
使われ方：一般 homotopy 極限の比較射・単位・余単位の正規化。 -/
lemma constantDiagramSourcePiZeroEquiv_class {Y : (operad A).Algebra}
    {F : K ⥤ (operad A).Algebra} (f : (Functor.const K).obj Y ⟶ F) :
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    constantDiagramSourcePiZeroEquiv A K Y F (constantDiagramSourceClass A K f) = Q.map f := by
  let := Diagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
  have hz : Q.map (constantDiagramFrameZeroIso A K Y).inv ≫
      Q.map (constantDiagramFrameZeroIso A K Y).hom = 𝟙 _ := by
    rw [← Q.map_comp, Iso.inv_hom_id, Q.map_id]
  have hc : ((constantDiagramLocalizedIso A K).app Y).inv ≫
      Q.map ((constantDiagramComparison A K).app Y) = 𝟙 _ :=
    ((constantDiagramLocalizedIso A K).app Y).inv_hom_id
  rw [constantDiagramSourceClass, constantDiagramSourcePiZeroEquiv_mk,
    constantDiagramFrameComparison_zero, Q.map_comp, Q.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map (constantDiagramFrameZeroIso A K Y).inv)
    (Q.map (constantDiagramFrameZeroIso A K Y).hom), hz, Category.id_comp,
    ← Category.assoc ((constantDiagramLocalizedIso A K).app Y).inv
      (Q.map ((constantDiagramComparison A K).app Y)), hc, Category.id_comp]

end SerrePositivity.EInfinity.BarrattEccles
