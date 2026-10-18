module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# 独立した二つの因子の射の引き戻し

概要：単体集合の独立した二つの因子の射が作る直積の四角形は引き戻しである。
方針：各次数の型で、二つの一致する成分から元の組を復元する。
規約：Segal 1974 Lemma 1.7 の円筒の境界の自然性を厳密な引き戻しとして扱う補助。
使われ方：境界包含と中央の対象の射の間の引き戻し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory

/--
概要：別の因子に作用する二射の可換な直積正方形は厳密な引き戻しである。
方針：型の引き戻しの一意性と存在を各単体次数で確認する。
規約：X⊗A→X⊗B と X⊗A→Y⊗A の四角形。
使われ方：円筒の境界包含の自然性の引き戻し性。
-/
theorem cartesianTensorSquare_isPullback {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B) :
    IsPullback (X ◁ g) (f ▷ A) (f ▷ B) (Y ◁ g) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, a⟩ ⟨y, b⟩ ⟨h₁, h₂⟩
    change (x, g.app d a) = (y, g.app d b) at h₁
    change (f.app d x, a) = (f.app d y, b) at h₂
    have hx : x = y := congrArg (fun p : X.obj d × B.obj d => p.1) h₁
    have ha : a = b := congrArg (fun p : Y.obj d × A.obj d => p.2) h₂
    exact Prod.ext hx ha
  · rintro ⟨x, b⟩ ⟨y, a⟩ h
    change (f.app d x, b) = (y, g.app d a) at h
    have hx : f.app d x = y := congrArg (fun p : Y.obj d × B.obj d => p.1) h
    have ha : b = g.app d a := congrArg (fun p : Y.obj d × B.obj d => p.2) h
    exact ⟨(x, a), Prod.ext rfl ha.symm, Prod.ext hx rfl⟩

end SerrePositivity.KST.Comparison
