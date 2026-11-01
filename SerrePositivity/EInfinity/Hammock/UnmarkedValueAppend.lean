module

public import SerrePositivity.EInfinity.Hammock.UnmarkedValueFlatten
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzag

/-!
# 元の hammock の貼り戻しによる文字列の連結

概要：元の二つの zigzag の連結の値は元の値の連結である。
方針：全列の端点移送を消去し、順序付き全列の回収式に代入する。
規約：両側の空語と長さ一の元の射も扱う。
使われ方：指定 prefix・非指定生成矢・残りの値の因子化。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y Z : Paths C}

lemma column_append_left (S : Zigzag W.paths a X Y) (T : Zigzag W.paths b Y Z)
    (i : Fin a.length) : column W (ZigzagAppend.obj S T) (i.castAdd b.length) = column W S i := by
  dsimp only [column, ZigzagAppend.obj]
  rw [Fin.addCases_left]
  exact GeneratorWord.erase_transport W _ _ (S.arrow i)

lemma column_append_right (S : Zigzag W.paths a X Y) (T : Zigzag W.paths b Y Z)
    (i : Fin b.length) : column W (ZigzagAppend.obj S T) (i.natAdd a.length) = column W T i := by
  dsimp only [column, ZigzagAppend.obj]
  rw [Fin.addCases_right]
  exact GeneratorWord.erase_transport W _ _ (T.arrow i)

lemma value_append (S : Zigzag W.paths a X Y) (T : Zigzag W.paths b Y Z) :
    value W (ZigzagAppend.obj S T) = value W S ++ value W T := by
  rw [value_flatten, value_flatten, value_flatten]
  change (List.ofFn (fun i : Fin (a.length + b.length) =>
    column W (ZigzagAppend.obj S T) i)).flatten = _
  rw [List.ofFn_add, List.flatten_append]
  apply congrArg₂ List.append
  · exact congrArg (fun f : Fin a.length → List (Quiver.Total C) => (List.ofFn f).flatten)
      (funext fun i => column_append_left W S T i)
  · exact congrArg (fun f : Fin b.length → List (Quiver.Total C) => (List.ofFn f).flatten)
      (funext fun i => column_append_right W S T i)

lemma value_forward {A B : Paths C} (p : A ⟶ B) :
    value W (ForwardZigzag.obj (W := W.paths) p) = GeneratorWord.erase W p := by
  rw [value_flatten]
  change (List.ofFn (fun _ : Fin 1 => GeneratorWord.erase W p)).flatten = _
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
