module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertexPaths

/-!
概要：指定した二つの射を、walking adjunctionの全頂点へ自由に延長する。
方針：実頂点から自由な道へ戻し、二つの生成射を評価する。
規約：零次元だけの構成であり、単位・余単位や高次の延長とは区別する。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の指定F・Uの保持。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実頂点の全ての射をその自由な道へ戻す。
方針：完全忠実な比較の原像を使う。
規約：対象は同じ二点。使われ方：Riehl–Verity Proposition 3.1.10 の零次元の逆比較。 -/
def walkingAdjunctionVertexToPath : WalkingAdjunctionVertex ⥤ Paths WalkingAdjunctionPoint where
  obj X := X.point
  map f := walkingAdjunctionPathFunctor.preimage f
  map_id X := by
    apply walkingAdjunctionPathFunctor.map_injective
    rw [Functor.map_preimage, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply walkingAdjunctionPathFunctor.map_injective
    rw [Functor.map_preimage, CategoryTheory.Functor.map_comp,
      Functor.map_preimage, Functor.map_preimage]

/-- 概要：自由な道へ戻しても全ての実頂点の射の像は変わらない。
方針：完全性の原像の照合を使う。規約：元の頂点の射。
使われ方：Riehl–Verity Proposition 3.1.10 の同じ零次元の比較。 -/
lemma walkingAdjunctionVertexToPath_map (X Y : WalkingAdjunctionVertex) (f : X ⟶ Y) :
    walkingAdjunctionPathFunctor.map (walkingAdjunctionVertexToPath.map f) = f :=
  walkingAdjunctionPathFunctor.map_preimage f

/-- 概要：実頂点の生成射を戻すと一段の道となる。
方針：忠実な比較へ送り、生成quiverの比較を計算する。
規約：二つの指定生成射を保持する。使われ方：HA Proposition 4.7.3.3 の指定F・U。 -/
lemma walkingAdjunctionVertexToPath_generator (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexToPath.map
      (X := ⟨X⟩) (Y := ⟨walkingAdjunctionOther X⟩) (walkingAdjunctionGeneratorVertex X) =
        (walkingAdjunctionGeneratingArrow X).toPath := by
  apply walkingAdjunctionPathFunctor.map_injective
  rw [walkingAdjunctionVertexToPath_map]
  change walkingAdjunctionGeneratorVertex X =
    (Paths.lift walkingAdjunctionGeneratorPrefunctor).map
      (walkingAdjunctionGeneratingArrow X).toPath
  rw [Paths.lift_toPath]
  cases X <;> rfl

variable {D : Type u} [Category.{v} D]

/-- 概要：指定したF・Uを二つの生成射の像とするquiverの写像。
方針：二点の像をC・Eとし、混合の生成射をF・Uとする。
規約：随伴の存在はここでは要らない。使われ方：Riehl–Verity Theorem 4.3.9 の始めのデータ。 -/
def walkingAdjunctionEvaluationPrefunctor (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    WalkingAdjunctionPoint ⥤q D where
  obj X := match X with
    | .plus => C
    | .minus => E
  map {X Y} e := by
    cases X <;> cases Y
    · exact (e.down rfl).elim
    · exact F
    · exact U
    · exact (e.down rfl).elim

/-- 概要：指定の二つの射を全ての実頂点の交互合成へ延長する。
方針：自由な道へ戻して生成射の写像を延長する。
規約：零次元の全合成を保つ実関手。高次延長の仮定は追加しない。
使われ方：HA Proposition 4.7.3.3 の同じF・Uを保持する全随伴の零次元。 -/
def walkingAdjunctionVertexEvaluation (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    WalkingAdjunctionVertex ⥤ D :=
  walkingAdjunctionVertexToPath ⋙ Paths.lift (walkingAdjunctionEvaluationPrefunctor C E F U)

/-- 概要：左の生成射の像は指定されたFそのもの。
方針：一段の道の評価を使う。規約：同型類だけの指定にしない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Theorem 4.3.9 のFの保持。 -/
lemma walkingAdjunctionVertexEvaluation_left (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    (walkingAdjunctionVertexEvaluation C E F U).map
      (X := ⟨.plus⟩) (Y := ⟨.minus⟩) (walkingAdjunctionGeneratorVertex .plus) = F := by
  change (Paths.lift (walkingAdjunctionEvaluationPrefunctor C E F U)).map
    (walkingAdjunctionVertexToPath.map
      (X := ⟨.plus⟩) (Y := ⟨.minus⟩) (walkingAdjunctionGeneratorVertex .plus)) = F
  rw [walkingAdjunctionVertexToPath_generator, Paths.lift_toPath]
  rfl

/-- 概要：右の生成射の像は指定されたUそのもの。
方針：もう一つの一段の道の評価を使う。規約：同じ射を保持する。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Theorem 4.3.9 のUの保持。 -/
lemma walkingAdjunctionVertexEvaluation_right (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    (walkingAdjunctionVertexEvaluation C E F U).map
      (X := ⟨.minus⟩) (Y := ⟨.plus⟩) (walkingAdjunctionGeneratorVertex .minus) = U := by
  change (Paths.lift (walkingAdjunctionEvaluationPrefunctor C E F U)).map
    (walkingAdjunctionVertexToPath.map
      (X := ⟨.minus⟩) (Y := ⟨.plus⟩) (walkingAdjunctionGeneratorVertex .minus)) = U
  rw [walkingAdjunctionVertexToPath_generator, Paths.lift_toPath]
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
