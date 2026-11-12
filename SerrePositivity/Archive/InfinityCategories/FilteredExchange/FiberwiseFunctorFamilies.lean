module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace

/-!
概要：fiber ごとの関手の全空間への任意の族の普遍性。
方針：底に重なる評価の族を curry し、定値図式の引き戻しへ入れる。
規約：底射を指定して保持する。
使われ方：定値底の path の収縮と比較写像の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open scoped Simplicial
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定された底射に重なる関手の族を全空間へ入れる。
方針：評価を curry し、底の定値図式との可換式を使う。
規約：全パラメータ。使われ方：底を固定したホモトピーの構成。 -/
def fiberwiseFunctorCurry {K T E B : SSet.{u}} (p : E ⟶ B) (b : T ⟶ B)
    (h : K ⊗ T ⟶ E) (hb : h ≫ p = snd K T ≫ b) : T ⟶ fiberwiseFunctorSpace p K :=
  pullback.lift (curry h) b (by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_comp_constantDiagram, hb])

/-- 概要：全空間に入れた族の関手成分は元の評価の curry。
方針：引き戻しの第一射影。規約：厳密な等式。使われ方：両端の評価の追跡。 -/
lemma fiberwiseFunctorCurry_fst {K T E B : SSet.{u}} (p : E ⟶ B) (b : T ⟶ B)
    (h : K ⊗ T ⟶ E) (hb : h ≫ p = snd K T ≫ b) :
    fiberwiseFunctorCurry p b h hb ≫ pullback.fst ((ihom K).map p) (constantDiagram K B) =
      curry h := pullback.lift_fst _ _ _

/-- 概要：全空間に入れた族の底射は元の指定射。
方針：引き戻しの第二射影。規約：全パラメータ。使われ方：底を保つホモトピー。 -/
lemma fiberwiseFunctorCurry_projection {K T E B : SSet.{u}} (p : E ⟶ B) (b : T ⟶ B)
    (h : K ⊗ T ⟶ E) (hb : h ≫ p = snd K T ≫ b) :
    fiberwiseFunctorCurry p b h hb ≫ fiberwiseFunctorProjection p K = b :=
  pullback.lift_snd _ _ _

/-- 概要：元の全空間から各 fiber の定値関手への切断。
方針：第二射影の後に元の底射を続ける。
規約：任意の形状 K。使われ方：path の始点評価の逆。 -/
def fiberwiseFunctorConstant {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    E ⟶ fiberwiseFunctorSpace p K :=
  fiberwiseFunctorCurry p p (snd K E) rfl

/-- 概要：定値関手の切断の底射は元の底射。
方針：族の底射の式。規約：厳密な等式。使われ方：底上の変形 retract。 -/
lemma fiberwiseFunctorConstant_projection {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    fiberwiseFunctorConstant p K ≫ fiberwiseFunctorProjection p K = p :=
  fiberwiseFunctorCurry_projection _ _ _ _

/-- 概要：定値関手の切断の関手成分は元の定値図式関手。
方針：族の第一射影を計算する。規約：厳密な等式。使われ方：path 収縮の始端。 -/
lemma fiberwiseFunctorConstant_fst {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    fiberwiseFunctorConstant p K ≫ pullback.fst ((ihom K).map p) (constantDiagram K B) =
      constantDiagram K E := fiberwiseFunctorCurry_fst _ _ _ _

/-- 概要：定値 path の切断の両端評価は元の全空間の恒等射。
方針：定値図式の各次数の評価を計算する。
規約：元の E。使われ方：始点評価の厳密な片逆。 -/
lemma fiberwiseFunctorConstant_endpoint {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    fiberwiseFunctorConstant p (Δ[1] : SSet.{u}) ≫ fiberwiseIntervalEndpoint p e = 𝟙 E := by
  rw [fiberwiseIntervalEndpoint, ← Category.assoc, fiberwiseFunctorConstant_fst]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change E.map (𝟙 n) x = x
  exact E.map_id_apply n x

end SerrePositivity.InfinityCategories.F2
