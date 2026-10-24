module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeDomainHomotopy
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionHomotopy
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomWhiskering

/-!
概要：全余錐から定値図式への射を、余錐単位と頂点側の制限で因子化する。
方針：底包含から右頂点への標準ホモトピーの自然性を使う。
規約：元の全余錐と指定した射を保持する。
使われ方：余極限関手の全パラメータ Hom 対応。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits SSet.Truncated.HomotopyCategory

/-- 概要：底制限は元の余錐の単位と右頂点への定値制限で因子化する。
方針：標準形状ホモトピーの自然性で、定値標的の成分を恒等射へ簡約する。
規約：全余錐から定値図式への元の射を使う。
使われ方：普遍余錐の Hom 対応と単位の照合。 -/
lemma precompositionHomotopy_constant_naturality {A B X : SSet.{u}}
    {f g : A ⟶ B} (T : SSet.Homotopy f g) (H : B ⟶ X) (y : X _⦋0⦌)
    (α : FunctorHom H (SSet.const y)) :
    (hoFunctor.map ((pre f).app X)).toFunctor.map α =
      homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp T H)) ≫
      (hoFunctor.map ((pre g).app X)).toFunctor.map α := by
  have hn := (F1B.precompositionNatTrans T X).naturality α
  erw [F1B.precompositionNatTrans_app, F1B.precompositionNatTrans_app] at hn
  have hc := F1B.homotopyHom_eqToHom
    (functorHomotopyPostcomp T (SSet.const y))
    (by simp only [SSet.comp_const]) (by simp only [functorHomotopyPostcomp, SSet.comp_const])
  rw [hc] at hn
  simp only [SSet.comp_const] at hn
  exact (Category.comp_id _).symm.trans hn

end SerrePositivity.InfinityCategories.F2.Presentable
