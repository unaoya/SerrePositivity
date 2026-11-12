module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplexColimit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplexes

/-!
概要：有限な単体集合からの射を有限部分複体の一段へ下ろす。
方針：有限部分複体の実際の filtered 余極限と有限表示性を使う。
規約：関手を通した因子分解では、その表示の余極限保存を明示的に要求する。
使われ方：Kan 置換の有限境界の因子分解。保存性自体の証明とは区別する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限形状からの射は有限部分複体を経由する。
方針：有限表示性を元の単体集合を頂点とする filtered 余極限に適用する。
規約：合成後の射は元の指定射そのもの。使われ方：有限データの有限な台。 -/
lemma finiteSubcomplex_factorization {K X : SSet.{u}} [K.Finite] (f : K ⟶ X) :
    ∃ A : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X, ∃ g : K ⟶ A.val, g ≫ A.val.ι = f := by
  obtain ⟨A, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplexCocone_isColimit X) f
  exact ⟨A, g, hg⟩

/-- 概要：有限部分複体表示を保存する関手の値への有限射は一段の像を経由する。
方針：保存された余極限余錐に有限表示性を適用する。
規約：Q の filtered 余極限保存を結論や定義に紛れ込ませず仮定として表示する。
使われ方：連続な Kan 置換を構成した後の有限境界の因子分解。 -/
lemma finiteSubcomplex_factorization_after_preserving_functor
    (Q : SSet.{u} ⥤ SSet.{u}) (X : SSet.{u})
    [PreservesColimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplexDiagram X) Q]
    {K : SSet.{u}} [K.Finite] (f : K ⟶ Q.obj X) :
    ∃ A : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X, ∃ g : K ⟶ Q.obj A.val, g ≫ Q.map A.val.ι = f := by
  obtain ⟨A, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (isColimitOfPreserves Q (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplexCocone_isColimit X)) f
  exact ⟨A, g, hg⟩

/-- 概要：関手の像への有限な相対写像は元の部分複体の後続段で境界を保って実現できる。
方針：写像を一段へ下ろし、有限な境界上の等式を共通の後続段で成立させる。
規約：Q の表示の保存を明示し、指定された境界の像は固定する。
使われ方：Kan 置換後の有限な境界条件の同時因子分解。 -/
lemma finiteSubcomplex_relative_factorization_after_preserving_functor
    (Q : SSet.{u} ⥤ SSet.{u}) (X : SSet.{u})
    [PreservesColimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplexDiagram X) Q]
    {A B : SSet.{u}} [A.Finite] [B.Finite] (i : A ⟶ B)
    (j : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X) (a : A ⟶ Q.obj j.val) (b : B ⟶ Q.obj X)
    (h : a ≫ Q.map j.val.ι = i ≫ b) :
    ∃ (k : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X) (v : j ⟶ k) (g : B ⟶ Q.obj k.val),
      i ≫ g = a ≫ Q.map (Subcomplex.homOfLE (leOfHom v)) ∧ g ≫ Q.map k.val.ι = b := by
  let hc := isColimitOfPreserves Q (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplexCocone_isColimit X)
  obtain ⟨l, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc b
  change g ≫ Q.map l.val.ι = b at hg
  obtain ⟨k, v, w, hw⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a (i ≫ g) (by
    change a ≫ Q.map j.val.ι = (i ≫ g) ≫ Q.map l.val.ι
    rw [Category.assoc, hg]
    exact h)
  change a ≫ Q.map (Subcomplex.homOfLE (leOfHom v)) =
    (i ≫ g) ≫ Q.map (Subcomplex.homOfLE (leOfHom w)) at hw
  refine ⟨k, v, g ≫ Q.map (Subcomplex.homOfLE (leOfHom w)), ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans hw.symm
  · rw [Category.assoc, ← Q.map_comp, Subcomplex.homOfLE_ι]
    exact hg

end SerrePositivity.InfinityCategories.Project.FilteredExchange
