module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionEnrichment
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
概要：walking adjunctionの頂点の圏と、二つの生成射からの自由な交互合成を照合する。
方針：頂点の長さと、自由な道の長さを比較する。
規約：高次の延長の存在は仮定しない。全随伴の零次元の指定を扱う。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Theorem 4.3.9。
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の生成射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全随伴の零次元の対象の包み。
方針：同じ二点を使う。規約：Hom圏の頂点を射とする圏構造を分離する。
使われ方：Riehl–Verity Proposition 3.1.10 の零次元の自由性。 -/
structure WalkingAdjunctionVertex where
  point : WalkingAdjunctionPoint

/-- 概要：構成済みの全随伴の頂点の圏。
方針：Hom圏の対象を射、水平合成の対象を合成とする。
規約：既存の単位と合成を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
instance walkingAdjunctionVertexCategory : Category WalkingAdjunctionVertex where
  Hom X Y := walkingAdjunctionHom X.point Y.point
  id X := walkingAdjunctionIdentity X.point
  comp {X Y Z} f g := (walkingAdjunctionHorizontal X.point Y.point Z.point).obj (f, g)
  id_comp {X Y} f := walkingAdjunctionHorizontal_obj_id_left X.point Y.point f
  comp_id {X Y} f := walkingAdjunctionHorizontal_obj_id_right X.point Y.point f
  assoc {W X Y Z} f g h :=
    walkingAdjunctionHorizontal_obj_assoc W.point X.point Y.point Z.point f g h

/-- 概要：二点の他方。
方針：二つの場合を交換する。規約：生成射の終点。
使われ方：Riehl–Verity Example 3.1.11 の二つの零次元生成射。 -/
def walkingAdjunctionOther : WalkingAdjunctionPoint → WalkingAdjunctionPoint
  | .plus => .minus
  | .minus => .plus

/-- 概要：二点の交換は対合。
方針：場合分けする。規約：同じ二対象。
使われ方：Riehl–Verity Proposition 3.1.10 の交互の語。 -/
lemma walkingAdjunctionOther_other (X : WalkingAdjunctionPoint) :
    walkingAdjunctionOther (walkingAdjunctionOther X) = X := by cases X <;> rfl

/-- 概要：異なる二点の間に一つずつの生成射を持つquiver。
方針：異なることの証明を持ち上げる。規約：自己生成射はない。
使われ方：Riehl–Verity Example 3.1.11 のfとu。 -/
instance walkingAdjunctionGeneratingQuiver : Quiver WalkingAdjunctionPoint where
  Hom X Y := PLift (X ≠ Y)

/-- 概要：二つの零次元生成射の実Hom内の値。
方針：混合Homの零単体の対象を取る。規約：元の水平合成と同じ向き。
使われ方：HA Proposition 4.7.3.3 の指定F・Uの始めの値。 -/
def walkingAdjunctionGeneratorVertex (X : WalkingAdjunctionPoint) :
    walkingAdjunctionHom X (walkingAdjunctionOther X) := by
  cases X
  · exact ⟨⦋0⦌⟩
  · exact ⟨⦋0⦌⟩

/-- 概要：自由な生成quiverから全随伴の頂点への写像。
方針：異なる二点を場合分けし、二つの実生成射へ送る。
規約：頂点の圏の合成を変えない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionGeneratorPrefunctor :
    WalkingAdjunctionPoint ⥤q WalkingAdjunctionVertex where
  obj X := ⟨X⟩
  map {X Y} e := by
    cases X <;> cases Y
    · exact (e.down rfl).elim
    · exact walkingAdjunctionGeneratorVertex .plus
    · exact walkingAdjunctionGeneratorVertex .minus
    · exact (e.down rfl).elim

/-- 概要：二つの生成射の全ての道を実際の頂点へ合成する。
方針：自由な道の普遍性を使う。規約：全生成語を対象とする。
使われ方：Riehl–Verity Proposition 3.1.10 の零次元の自由性の比較。 -/
def walkingAdjunctionPathFunctor :
    Paths WalkingAdjunctionPoint ⥤ WalkingAdjunctionVertex :=
  Paths.lift walkingAdjunctionGeneratorPrefunctor

/-- 概要：頂点の交互合成の長さ。
方針：自己Homは個数の2倍、混合Homは次元の2倍+1。
規約：恒等射の長さは0。使われ方：Riehl–Verity Example 3.1.11 の零次元の語。 -/
def walkingAdjunctionVertexLength : (X Y : WalkingAdjunctionPoint) →
    walkingAdjunctionHom X Y → ℕ
  | .plus, .plus, A => 2 * augmentedOrdinalCard A
  | .plus, .minus, A => 2 * A.obj.len + 1
  | .minus, .plus, A => 2 * A.obj.len + 1
  | .minus, .minus, A => 2 * augmentedOrdinalCard A.unop

/-- 概要：語の長さと既存の重みの比較。
方針：四Homを場合分けする。規約：端点の補正を明記する。
使われ方：Riehl–Verity Proposition 3.1.10 の合成の長さ。 -/
lemma walkingAdjunctionVertexLength_weight (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionVertexLength X Y A + walkingAdjunctionTargetCorrection X =
      2 * walkingAdjunctionWeight X Y A + walkingAdjunctionTargetCorrection Y := by
  cases X <;> cases Y <;>
    simp only [walkingAdjunctionVertexLength, walkingAdjunctionWeight,
      walkingAdjunctionTargetCorrection]; omega

/-- 概要：全水平合成の頂点の長さは加法的。
方針：重みの加法則と端点の補正の相殺を使う。
規約：全八合成を含む。使われ方：Riehl–Verity Proposition 3.1.10 の語の合成。 -/
lemma walkingAdjunctionVertexLength_comp (X Y Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) (B : walkingAdjunctionHom Y Z) :
    walkingAdjunctionVertexLength X Z ((walkingAdjunctionHorizontal X Y Z).obj (A, B)) =
      walkingAdjunctionVertexLength X Y A + walkingAdjunctionVertexLength Y Z B := by
  have hs := walkingAdjunctionHorizontal_weight X Y Z A B
  have h₁ := walkingAdjunctionVertexLength_weight X Y A
  have h₂ := walkingAdjunctionVertexLength_weight Y Z B
  have h₃ := walkingAdjunctionVertexLength_weight X Z
    ((walkingAdjunctionHorizontal X Y Z).obj (A, B))
  omega

/-- 概要：同じ端点では語の長さは頂点を区別する。
方針：重みの単射性へ帰着する。規約：全ての頂点を含む。
使われ方：Riehl–Verity Proposition 3.1.10 の語の一意性。 -/
lemma walkingAdjunctionVertexLength_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionVertexLength X Y) := by
  intro A B h
  apply walkingAdjunctionWeight_injective X Y
  have h₁ := walkingAdjunctionVertexLength_weight X Y A
  have h₂ := walkingAdjunctionVertexLength_weight X Y B
  omega

/-- 概要：恒等語の長さは0。
方針：二点の空の自己Homを計算する。規約：同じ単位。
使われ方：Riehl–Verity Proposition 3.1.10 の空の語。 -/
lemma walkingAdjunctionVertexLength_id (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexLength X X (walkingAdjunctionIdentity X) = 0 := by
  cases X <;> rfl

/-- 概要：二つの生成語の長さは1。
方針：両方とも混合Homの次元0。規約：実際の生成射。
使われ方：Riehl–Verity Example 3.1.11。 -/
lemma walkingAdjunctionVertexLength_generator (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexLength X (walkingAdjunctionOther X)
      (walkingAdjunctionGeneratorVertex X) = 1 := by
  cases X <;> rfl

/-- 概要：生成quiverの各射の実像の長さ。
方針：端点を場合分けする。規約：自己射は存在しない。
使われ方：Riehl–Verity Proposition 3.1.10 の自由な道の長さの比較。 -/
lemma walkingAdjunctionVertexLength_prefunctor {X Y : WalkingAdjunctionPoint} (e : X ⟶ Y) :
    walkingAdjunctionVertexLength X Y (walkingAdjunctionGeneratorPrefunctor.map e) = 1 := by
  cases X <;> cases Y
  · exact (e.down rfl).elim
  · rfl
  · rfl
  · exact (e.down rfl).elim

/-- 概要：自由な道の長さは実像の頂点の長さと一致する。
方針：道の帰納法と全合成の長さの加法則を使う。
規約：全ての有限の道。使われ方：Riehl–Verity Proposition 3.1.10 の零次元の比較。 -/
lemma walkingAdjunctionPathFunctor_length {X Y : WalkingAdjunctionPoint} (p : Quiver.Path X Y) :
    walkingAdjunctionVertexLength X Y (walkingAdjunctionPathFunctor.map p) = p.length := by
  induction p with
  | nil => exact walkingAdjunctionVertexLength_id X
  | @cons Y Z p e ih =>
    change walkingAdjunctionVertexLength X Z
      ((walkingAdjunctionHorizontal X Y Z).obj
        (walkingAdjunctionPathFunctor.map p, walkingAdjunctionGeneratorPrefunctor.map e)) = _
    rw [walkingAdjunctionVertexLength_comp, ih, walkingAdjunctionVertexLength_prefunctor]
    rfl

end SerrePositivity.InfinityCategories.HA.Monads
