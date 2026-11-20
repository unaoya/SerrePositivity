module


public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 細分の標準単体による被覆

概要：単体集合の細分の任意の単体は、元の一つの標準単体の細分に由来する。
方針：標準単体による密度の余錐を、細分と次数評価の余極限保存で移す。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分比較の単射性への補助。
使われ方：実際の horn の細分の元を余面からの表示へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：細分の各単体は、一つの標準単体からの写像を細分した像に入る。
方針：ULift Yoneda の密度の余極限と、型の余極限の共同全射性を使う。
規約：細分が左随伴であること以外のホモトピー論的仮定は不要。
使われ方：細分の包含の単射性を標準単体上の表示で確認する。
-/
theorem subdivisionSimplexCover (X : SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (s : (SSet.sd.obj X).obj d) :
    ∃ (m : SimplexCategory) (f : SSet.stdSimplex.obj m ⟶ X)
      (t : (SSet.sd.obj (SSet.stdSimplex.obj m)).obj d), (SSet.sd.map f).app d t = s := by
  let F := SSet.sd ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
  have hc := isColimitOfPreserves F (Presheaf.isColimitTautologicalCocone'.{u} X)
  obtain ⟨a, t, ht⟩ := Types.jointly_surjective_of_isColimit hc s
  exact ⟨a.left, a.hom, t, ht⟩

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
