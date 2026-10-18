module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 二つのファイバー模型の共通の trivial fibration の模型

概要：同じ基底上の二つの Kan fibration への局所化同型を、共通の trivial fibration で比較する。
方針：二つの模型の積への射を anodyne–Kan 分解し、各射影の可逆性と持ち上げ性を示す。
規約：Segal 1974 Lemma 1.7 の厳密化への補助。Mather 1976 の WCHP の経路とは異なる。
使われ方：二つの厳密ファイバーを、端点の全空間へ延長できる共通模型で置き換える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/--
概要：二つの Kan なファイバー模型への局所化同型は、共通の trivial fibration の模型に持ち上がる。
方針：基底上の積への同時比較を分解し、射影の Kan 性と局所化可逆性から全単射的右持ち上げ性を得る。
規約：trivial fibration は全ての単射に対する右持ち上げ性で指定する。
使われ方：単射に沿う trivial fibration の延長を二つの端点へ適用する前段。
-/
theorem commonTrivialFibrationRefinement {Y A B C : SSet.{u}}
    [SSet.KanComplex A] [SSet.KanComplex B]
    (p : A ⟶ C) (q : B ⟶ C)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (hq : SSet.modelCategoryQuillen.J.rlp q)
    (a : Y ⟶ A) (b : Y ⟶ B) (hab : a ≫ p = b ≫ q)
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b)) :
    ∃ (Z : SSet.{u}) (i : Y ⟶ Z) (r : Z ⟶ A) (s : Z ⟶ B),
      SSet.anodyneExtensions i ∧ i ≫ r = a ∧ i ≫ s = b ∧ r ≫ p = s ≫ q ∧
      (MorphismProperty.monomorphisms SSet.{u}).rlp r ∧
      (MorphismProperty.monomorphisms SSet.{u}).rlp s := by
  let v : Y ⟶ pullback p q := pullback.lift a b hab
  let d := AnodyneKanReplacement.factorization.factorizationData v
  let r := d.p ≫ pullback.fst p q
  let s := d.p ≫ pullback.snd p q
  have hir : d.i ≫ r = a := by
    dsimp only [r]
    rw [← Category.assoc, d.fac]
    exact pullback.lift_fst ..
  have his : d.i ≫ s = b := by
    dsimp only [s]
    rw [← Category.assoc, d.fac]
    exact pullback.lift_snd ..
  have hr : SSet.modelCategoryQuillen.J.rlp r :=
    SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ d.hp
      (SSet.modelCategoryQuillen.J.rlp.pullback_fst p q hq)
  have hs : SSet.modelCategoryQuillen.J.rlp s :=
    SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ d.hp
      (SSet.modelCategoryQuillen.J.rlp.pullback_snd p q hp)
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map d.i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ d.hi
  have hri : IsIso (AnodyneHomotopy.anodyneQ.map r) := by
    have hcomp : IsIso (AnodyneHomotopy.anodyneQ.map d.i ≫ AnodyneHomotopy.anodyneQ.map r) := by
      rw [← Functor.map_comp, hir]
      exact ha
    exact (isIso_comp_left_iff _ _).mp hcomp
  have hsi : IsIso (AnodyneHomotopy.anodyneQ.map s) := by
    have hcomp : IsIso (AnodyneHomotopy.anodyneQ.map d.i ≫ AnodyneHomotopy.anodyneQ.map s) := by
      rw [← Functor.map_comp, his]
      exact hb
    exact (isIso_comp_left_iff _ _).mp hcomp
  refine ⟨d.Z, d.i, r, s, d.hi, hir, his, ?_, ?_, ?_⟩
  · dsimp only [r, s]
    rw [Category.assoc, Category.assoc, pullback.condition]
  · exact KanFibrationLocalizedLifting.of_localized_isIso r hr
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) hri
  · exact KanFibrationLocalizedLifting.of_localized_isIso s hs
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) hsi

end SerrePositivity.KST.Comparison
