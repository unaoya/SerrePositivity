module
public import SerrePositivity.InfinityCategories.Stable.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagramArrows

/-! # Coslice の余錐図式と終点評価

概要：coslice から余錐図式の関手単体集合への射は、余錐頂点での評価と厳密に可換。
方針：普遍余錐の直積表示を右包含に制限し、curry と一点評価を計算する。
規約：値域の quasicategory 性は不要。使われ方：余極限の標準比較を四角形の比較へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice の余錐を関手単体集合の図式へ写す。
方針：固定図式上の余錐の族への比較を全図式に含める。
規約：余錐の形状は K⋆Δ[0]。使われ方：coslice の射の図式としての表示。 -/
def cosliceCoconeDiagramMap {K X : SSet.{u}} (p : K ⟶ X) :
    sliceUnder p ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X :=
  cosliceCoconeFamilyMap p ≫ vertexFiberι (coconeRestriction K X) (functorVertex p)

/-- 概要：coslice の図式表示の零次成分は元の余錐の関手頂点表示。
方針：固定図式上の族への比較の零次成分を使う。
規約：余錐全体の値を保つ。使われ方：比較の両端の同定。 -/
lemma cosliceCoconeDiagramMap_vertex {K X : SSet.{u}} (p : K ⟶ X) (c : JoinCocone p) :
    (cosliceCoconeDiagramMap p).app (Opposite.op ⦋0⦌) c = functorVertex c.val :=
  congrArg Subtype.val (cosliceCoconeFamilyMap_app_zero p c)

/-- 概要：coslice の図式表示を元の図式に制限すると固定した図式に定値となる。
方針：fiber の包含と制限の合成を計算する。
規約：全単体で厳密。使われ方：比較図式が基底を固定することの検査。 -/
lemma cosliceCoconeDiagramMap_restriction {K X : SSet.{u}} (p : K ⟶ X) :
    cosliceCoconeDiagramMap p ≫ coconeRestriction K X = SSet.const (functorVertex p) := by
  change curry (cosliceCoconeFamilyUncurry p) ≫ coconeRestriction K X = _
  exact cosliceCoconeFamilyUncurry_curry_fixed p

/-- 概要：普遍余錐の直積族を頂点因子へ制限すると coslice の終点射影になる。
方針：join と直積の比較の右包含の式と、uncurry の右端評価を使う。
規約：標準零単体の因子は第二射影で忘れる。使われ方：関手単体集合での頂点評価。 -/
lemma cosliceCoconeFamilyUncurry_inr {K X : SSet.{u}} (p : K ⟶ X) :
    (joinInr K (Δ[0] : SSet.{u}) ▷ sliceUnder p) ≫ cosliceCoconeFamilyUncurry p =
      snd Δ[0] (sliceUnder p) ≫ sliceUnderProjection p := by
  unfold cosliceCoconeFamilyUncurry
  rw [← Category.assoc, joinTensorRight_inr]
  rw [← Category.assoc, joinInr_joinMap, Category.assoc, sliceUnderUncurry_projection,
    Category.id_comp]

/-- 概要：余錐の図式表示を頂点で評価すると元の coslice の終点射影になる。
方針：右包含に制限した curry を一点で評価する。
規約：値域に追加仮定なし。使われ方：colimitVertexIso と図式比較の頂点成分の同定。 -/
lemma cosliceCoconeDiagramMap_vertexEvaluation {K X : SSet.{u}} (p : K ⟶ X) :
    cosliceCoconeDiagramMap p ≫ evaluateFunctorAt (Y := X)
      ((joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) =
    sliceUnderProjection p := by
  rw [← stable_pre_evaluateFunctorAt (joinInr K (Δ[0] : SSet.{u}))]
  rw [← Category.assoc]
  have h : cosliceCoconeDiagramMap p ≫ (pre (joinInr K (Δ[0] : SSet.{u}))).app X =
      curry (snd Δ[0] (sliceUnder p) ≫ sliceUnderProjection p) := by
    apply uncurry_injective
    change uncurry (curry (cosliceCoconeFamilyUncurry p) ≫ _) = _
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, cosliceCoconeFamilyUncurry_inr]
  rw [h, curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd, Category.id_comp]

end SerrePositivity.InfinityCategories
