module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryPost

/-!
概要：底と終点を固定した全余錐を、指定評価の全余錐の下でさらに固定する。
方針：指定評価の同じ全写像上の実 fiber を取り、可換な後合成を移す。
規約：三つの固定条件を保持し、通常の余錐同型に弱めない。
使われ方：Ind の始点評価の下で、区間の宇宙比較を戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X Y Z : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
  (e : X ⟶ Z) (s : join A (Δ[0] : SSet.{u}) ⟶ Z)
/-- 概要：指定評価による全余錐も固定した、同じ余錐の実 fiber。
方針：同じ評価の全射の fiber を取る。規約：全係数を保持。使われ方：相対比較。 -/
def fixedCoconeBoundaryUnder : SSet.{u} :=
  vertexFiber (fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map e)
    (functorVertex s)
/-- 概要：指定評価と可換する後合成は、元の三固定条件を全て保つ。
方針：内部 Hom の合成則を使う。規約：評価後の全余錐を保持。使われ方：宇宙比較。 -/
def fixedCoconeBoundaryUnderPost (h : X ⟶ Y) (e' : Y ⟶ Z) (he : h ≫ e' = e) :
    fixedCoconeBoundaryUnder p b e s ⟶ fixedCoconeBoundaryUnder (p ≫ h) (b ≫ h) e' s :=
  vertexFiberLift _ _
    (vertexFiberι (fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map e)
      (functorVertex s) ≫ fixedCoconeBoundaryPost p b h) (by
    have hp : fixedCoconeBoundaryPost p b h ≫
        fixedCoconeBoundaryInclusion (p ≫ h) (b ≫ h) =
        fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map h :=
      vertexFiberLift_ι _ _ _ _
    rw [Category.assoc, ← Category.assoc (fixedCoconeBoundaryPost p b h), hp]
    simp only [Category.assoc]
    rw [← Functor.map_comp, he]
    exact vertexFiberι_comp _ _)
/-- 概要：三固定条件を保った後合成の頂点は、元の全余錐の後合成そのもの。
方針：同じ内部 Hom の頂点を計算する。規約：指定全射を保持。使われ方：端点照合。 -/
lemma fixedCoconeBoundaryUnderPost_vertex_val
    (h : X ⟶ Y) (e' : Y ⟶ Z) (he : h ≫ e' = e)
    (v : (fixedCoconeBoundaryUnder p b e s) _⦋0⦌) (c : join A Δ[0] ⟶ X)
    (hv : v.val.val = functorVertex c) :
    ((fixedCoconeBoundaryUnderPost p b e s h e' he).app (Opposite.op ⦋0⦌) v).val.val =
      functorVertex (c ≫ h) := by
  change ((ihom (join A Δ[0])).map h).app _ v.val.val = _
  rw [hv]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
