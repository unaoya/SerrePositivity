module
public import SerrePositivity.KST.SConstruction.ConcreteCubeSignature
public import SerrePositivity.KST.SConstruction.CubeJoinNormalForm

/-! # 具体的な cubical 射の有限 max 正規形
概要：生成条件を保つ元の射を、一意な有限 max 表示へ単射で送る。
方針：join 保存による全頂点の回収式を適用し、合成も同じ評価から計算する。
規約：全ての有限 max 表示が cubical 射であるとは主張しない。
使われ方：具体的な立方体圏と Serre 鎖立方体の表示非依存性の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的な cubical 射から回収した有限 max 表示。 -/
def concreteCubeNormalForm {X Y : ConcreteCube} (f : X ⟶ Y) :
    CubeJoinNormalForm X.dimension Y.dimension :=
  cubeJoinNormalFormOfMap f.val

/-- 元の cubical 射は、同じ射の有限 max 表示を評価して回収される。 -/
lemma concreteCubeNormalForm_eval {X Y : ConcreteCube} (f : X ⟶ Y)
    (x : CubeVertex X.dimension) :
    cubeJoinNormalFormEval (concreteCubeNormalForm f) x = f.val x :=
  cubeJoinNormalFormOfMap_eval (cubeMapGenerated_sup f.property) x

/-- 有限 max 表示は具体的な cubical 射の等号を検出する。 -/
lemma concreteCubeNormalForm_injective (X Y : ConcreteCube) :
    Function.Injective (concreteCubeNormalForm (X := X) (Y := Y)) := by
  intro f g h
  apply Subtype.ext
  funext x
  rw [← concreteCubeNormalForm_eval f x, ← concreteCubeNormalForm_eval g x, h]

/-- 具体的な cubical 射の等号と、同じ有限 max 表示の等号の同値。 -/
lemma concreteCubeNormalForm_eq_iff {X Y : ConcreteCube} (f g : X ⟶ Y) :
    concreteCubeNormalForm f = concreteCubeNormalForm g ↔ f = g :=
  (concreteCubeNormalForm_injective X Y).eq_iff

/-- 元の合成の有限 max 表示は、同じ二つの表示の評価の合成から回収される。 -/
lemma concreteCubeNormalForm_comp {X Y Z : ConcreteCube} (f : X ⟶ Y) (g : Y ⟶ Z) :
    concreteCubeNormalForm (f ≫ g) = cubeJoinNormalFormOfMap
      (fun x => cubeJoinNormalFormEval (concreteCubeNormalForm g)
        (cubeJoinNormalFormEval (concreteCubeNormalForm f) x)) := by
  apply congrArg cubeJoinNormalFormOfMap
  funext x
  rw [concreteCubeNormalForm_eval, concreteCubeNormalForm_eval]
  rfl

end SerrePositivity.KST.SConstruction
