module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplicialCoproductMono

/-!
# 余積と局所化可逆な射

概要：単体集合の二項余積は局所化可逆な射を保つ。
方針：片側の恒等射との余積を単射に沿う pushout とし、対称性と合成を使う。
規約：Segal 1974 Lemma 1.7 の二重写像円筒の模型の比較の補助。
使われ方：二重写像円筒の両端の余積の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：局所化可逆な射と恒等射の余積は局所化可逆である。
方針：余積の包含に沿った pushout の左固有性を使う。
規約：余積の包含は単体集合の単射である。
使われ方：二つの可逆な成分を持つ余積の比較。
-/
theorem coprodMap_left_localized_isIso {A A' : SSet.{u}} (a : A ⟶ A')
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a)) (B : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coprod.map a (𝟙 B))) :=
  KanLocalizedLeftProper.localized_isIso a ha coprod.inl coprod.inl (coprod.map a (𝟙 B))
    (IsPushout.of_coprod_inl_with_id a B).flip

/--
概要：恒等射と局所化可逆な射の余積は局所化可逆である。
方針：余積の対称性で前の補題に移す。
規約：比較の同型は実際の余積の braiding を使う。
使われ方：二つの可逆な成分を持つ余積の比較。
-/
theorem coprodMap_right_localized_isIso {B B' : SSet.{u}} (b : B ⟶ B')
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b)) (A : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coprod.map (𝟙 A) b)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have := coprodMap_left_localized_isIso b hb A
  have h : coprod.map (𝟙 A) b ≫ (coprod.braiding A B').hom =
      (coprod.braiding A B).hom ≫ coprod.map b (𝟙 A) := by
    apply coprod.hom_ext <;> simp [coprod.braiding]
  have he := congrArg Q.map h
  rw [Q.map_comp, Q.map_comp] at he
  have hc : IsIso (Q.map (coprod.map (𝟙 A) b) ≫ Q.map (coprod.braiding A B').hom) :=
    he.symm ▸ inferInstanceAs (IsIso (Q.map (coprod.braiding A B).hom ≫ Q.map (coprod.map b (𝟙 A))))
  exact (isIso_comp_right_iff _ _).mp hc

/--
概要：二つの局所化可逆な射の余積は局所化可逆である。
方針：片側を変える二つの余積の写像へ分解する。
規約：実際の二項余積の比較射について述べる。
使われ方：二重写像円筒の始域と両端の比較。
-/
theorem coprodMap_localized_isIso {A B A' B' : SSet.{u}} (a : A ⟶ A') (b : B ⟶ B')
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coprod.map a b)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have := coprodMap_left_localized_isIso a ha B
  have := coprodMap_right_localized_isIso b hb A'
  have h : coprod.map a (𝟙 B) ≫ coprod.map (𝟙 A') b = coprod.map a b := by simp
  rw [← h, Q.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
