module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.HomWeightUnitEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：指定 Hom と指定同型の curry が、元の合成を保存することを正規化して示す。
方針：端点移送を除いて同じ関手空間の Hom 作用へ戻す。
規約：元の射と元の同型を保持する。
使われ方：P-12 の共同切断比較の合成を図式値の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：正規化 Hom 作用は、同じ中間端点を持つ射の合成を保存する。
方針：端点等式を消去し、元のホモトピー圏の関手の合成則を使う。
規約：指定した端点表示を使う。使われ方：curry の合成則の一般形。 -/
lemma normalizedVertexHomMap_hom_comp {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y z : X _⦋0⦌} {x' y' z' : Y _⦋0⦌}
    (hx : x' = f.app (Opposite.op ⦋0⦌) x)
    (hy : y' = f.app (Opposite.op ⦋0⦌) y)
    (hz : z' = f.app (Opposite.op ⦋0⦌) z)
    (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (β : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z) :
    normalizedVertexHomMap f hx hz (α ≫ β) =
      normalizedVertexHomMap f hx hy α ≫ normalizedVertexHomMap f hy hz β := by
  subst x' y' z'
  simp only [normalizedVertexHomMap, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (hoFunctor.map f).toFunctor.map_comp α β

/-- 概要：指定した二つの全自然変換の curry は元の合成を保存する。
方針：正規化された同じ関手空間の Hom 作用の合成則を使う。
規約：元の中間図式を保持する。使われ方：共同比較の合成を curry する。 -/
lemma curryFunctorHom_comp {A B X : SSet.{u}} {f g h : A ⊗ B ⟶ X}
    (α : FunctorHom f g) (β : FunctorHom g h) :
    curryFunctorHom (α ≫ β) = curryFunctorHom α ≫ curryFunctorHom β := by
  simp only [curryFunctorHom_eq_normalizedMap]
  exact normalizedVertexHomMap_hom_comp _ _ _ _ α β

/-- 概要：指定同型の curry は同じ関手空間の curry による頂点同型の像。
方針：curry の定義中の型移送を異種等式として切り離す。
規約：元の指定同型を使う。使われ方：順方向の Hom と curry の照合。 -/
lemma functorIsoCurry_heq_map {A B X : SSet.{u}} [Quasicategory X]
    {f g : A ⊗ B ⟶ X} (e : FunctorIso f g) :
    HEq e.curry (VertexIso.map e (functorSpaceCurryMap A B X)) := by
  unfold FunctorIso.curry
  dsimp only [_root_.id]
  have hcast {T U : Sort (u + 1)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 概要：頂点等式で同定した同じ同型の順方向の射も異種等式で一致する。
方針：二つの端点等式と同型の異種等式を消去する。
規約：元の同型を保持する。使われ方：同型の curry と Hom の curry の照合。 -/
lemma vertexIso_hom_heq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {e : VertexIso x y} {e' : VertexIso x' y'}
    (h : HEq e e') : HEq e.hom e'.hom := by
  subst x' y'
  cases eq_of_heq h
  rfl

/-- 概要：指定同型を curry した順方向の射は同じ指定 Hom の curry。
方針：両表示を未正規化の同じ関手の Hom 作用と比較する。
規約：同じ端点等式を使う。使われ方：共同比較同型の合成の正規化。 -/
lemma functorIsoCurry_hom {A B X : SSet.{u}} [Quasicategory X]
    {f g : A ⊗ B ⟶ X} (e : FunctorIso f g) :
    e.curry.hom = curryFunctorHom e.hom := by
  have h := vertexIso_hom_heq (functorSpaceCurryMap_vertex f).symm
    (functorSpaceCurryMap_vertex g).symm (functorIsoCurry_heq_map e)
  exact eq_of_heq (h.trans (curryFunctorHom_heq_map e.hom).symm)

/-- 概要：指定同型の curry は元の同型の合成を保存する。
方針：順方向の Hom の同定と、その curry の合成保存を使う。
規約：同型を選び直さない。使われ方：共同切断比較の合成の curry。 -/
lemma functorIsoCurry_trans {A B X : SSet.{u}} [Quasicategory X]
    {f g h : A ⊗ B ⟶ X} (e : FunctorIso f g) (d : FunctorIso g h) :
    FunctorIso.curry (e ≪≫ d) = e.curry ≪≫ d.curry := by
  apply Iso.ext
  simp only [functorIsoCurry_hom, Iso.trans_hom]
  exact curryFunctorHom_comp e.hom d.hom

end SerrePositivity.InfinityCategories.F2.Presentable
