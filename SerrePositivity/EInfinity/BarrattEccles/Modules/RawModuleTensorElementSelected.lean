module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementLinear

/-!
# 元の全要素列の選択した高次 cochain

概要：M10 の同じ全普遍 cochain を任意の有限部分集合の終端へ制限する。
方針：同じ昇順列挙と検証済みの全単射成分式を使う。
規約：HA Construction 1.3.1.6、元の部分集合・次数・終端射を保持する。
使われ方：元の全係数 cone の始点を含む実高次成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の有限部分集合の同じ昇順単体作用素。
方針：既存の昇順列挙を同じ単体射にする。
規約：HA 1.3.1.6、同じ像。使われ方：元の高次 cochain の選択。 -/
abbrev strictRawModuleTensorElementSelection {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) : ⦋J.card - 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom (J.orderEmbOfFin
    (show J.card = J.card - 1 + 1 by have := Finset.card_pos.mpr hJ; omega)).toOrderHom

/-- 概要：同じ選択単体の終端は元の部分集合の最大元。
方針：既存の昇順列挙の終端式を使う。
規約：HA 1.3.1.6、同じ端点。使われ方：cochain の元の終端への移送。 -/
lemma strictRawModuleTensorElementSelection_last {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) :
    (strictRawModuleTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)) =
      J.max' hJ := by
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  exact Finset.orderEmbOfFin_last hc (by omega)

/-- 概要：同じ選択列の元の最上位普遍 cochain。
方針：同じ全列を昇順列挙で制限し、同じ最上位成分を取る。
規約：HA 1.3.1.6、正しい全次数。使われ方：全 cone の混合成分。 -/
def strictRawModuleTensorElementSelectedCochain {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj
        (c.obj ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))) k :=
  (strictRawModuleTensorElementLinear A X P Q
    ((SimplexCategory.toCat.map (strictRawModuleTensorElementSelection J hJ)).toFunctor ⋙ c)).val.component
      Finset.univ k Finset.univ_nonempty (by
        have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
        simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk)

/-- 概要：同じ選択 cochain の終端射による像は元の像部分集合の成分。
方針：元の全単射再添字成分式に同じ昇順列挙を代入する。
規約：HA 1.3.1.6、同じ成分。使われ方：全 cone の削除・合成項の照合。 -/
lemma strictRawModuleTensorElementSelectedCochain_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))))).f k
      (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk := by
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hd : k = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk
  have h := strictRawModuleTensorElementLinear_component_inj A X P Q c
    (strictRawModuleTensorElementSelection J hJ) Finset.univ k Finset.univ_nonempty hd
    (J.orderEmbOfFin hc).injective.injOn
  have hi : (Finset.univ : Finset (Fin (J.card - 1 + 1))).image
      (strictRawModuleTensorElementSelection J hJ).toOrderHom = J := J.image_orderEmbOfFin_univ hc
  simpa only [strictRawModuleTensorElementSelectedCochain, hi] using h

/-- 概要：同じ選択 cochain を元の最大元の係数へ移す。
方針：同じ終端等式で元の型を移送する。
規約：HA 1.3.1.6、同じ cochain。使われ方：全 cone の指定端点。 -/
def strictRawModuleTensorElementSelectedCochainAtMax {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k :=
  cast (by rw [strictRawModuleTensorElementSelection_last])
    (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk)

end SerrePositivity.EInfinity.BarrattEccles
