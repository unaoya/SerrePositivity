module

public import SerrePositivity.EInfinity.Hammock.UnmarkedValueAppend
public import SerrePositivity.EInfinity.Hammock.UnmarkedRefinementRecovery
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedPrefix

/-!
# 元の最初の切断の三因子の文字列評価

概要：指定 prefix は空、中央の生成矢は同じ一文字、全体は元の値に戻る。
方針：元の全列の指定性、貼り戻しの連結則と元の refinedFunctor の回収を使う。
規約：全行で元の同じ生成矢・prefix・残りを保持する。
使われ方：残りの文字列が元の先頭を除いたものになる式と長さの反復。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ [])

lemma prefix_value (d : Fin (n.unop.len + 1)) : value W ((functor W τ h).obj d) = [] :=
  value_eq_nil_of_marked W _ (arrow_mem W τ h d)

lemma generator_value (d : Fin (n.unop.len + 1)) :
    value W ((Attachments.generatorBlock W τ (index W τ h) (nonempty W τ h)).obj d) =
      [rowGenerator W τ (index W τ h) (nonempty W τ h)] := by
  classical
  rw [show ((Attachments.generatorBlock W τ (index W τ h) (nonempty W τ h)).obj d) =
    ForwardZigzag.obj ((rowGeneratorMap W τ (index W τ h) (nonempty W τ h)).app d) from rfl,
    value_forward]
  change (if W (rowGenerator W τ (index W τ h) (nonempty W τ h)).hom then [] else
    [] ++ [rowGenerator W τ (index W τ h) (nonempty W τ h)]) = _
  rw [ite_eq_right (fixedRowCut W τ (index W τ h) (nonempty W τ h) d).unmarked]
  rfl

lemma refined_value (d : Fin (n.unop.len + 1)) :
    value W ((Attachments.refinedFunctor W τ (index W τ h) (nonempty W τ h)).obj d) =
      value W (τ.obj d) := by
  have hr := congrArg (fun F => F.obj d)
    (Attachments.refinedFunctor_recovery W τ (index W τ h) (nonempty W τ h))
  exact (value_wordAction W
    (Attachments.refinementMap W τ (index W τ h) (nonempty W τ h))
    ((Attachments.refinedFunctor W τ (index W τ h) (nonempty W τ h)).obj d)).symm.trans
      (congrArg (value W) hr)

lemma value_cons_residual (d : Fin (n.unop.len + 1)) : value W (τ.obj d) =
    rowGenerator W τ (index W τ h) (nonempty W τ h) ::
      value W ((Attachments.residualFunctor W τ (index W τ h) (nonempty W τ h)).obj d) := by
  rw [← refined_value W τ h d]
  change value W (ZigzagAppend.obj (ZigzagAppend.obj
    ((functor W τ h).obj d)
    ((Attachments.generatorBlock W τ (index W τ h) (nonempty W τ h)).obj d))
    ((Attachments.residualFunctor W τ (index W τ h) (nonempty W τ h)).obj d)) = _
  rw [value_append, value_append, prefix_value, generator_value]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
