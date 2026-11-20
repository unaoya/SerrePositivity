module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-! # 内部 uncurry の行と列の厳密な制限
概要：二重内部 Hom を積の内部 Hom に戻した後の行・列の制限を評価と照合する。
方針：内部 Hom の単体を計算し、固定頂点の定値単体の自然性を使う。
規約：添字・標的は任意の単体集合。使われ方：二重 cofiber 四角形の辺の抽出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 固定頂点での評価は閉構造の評価への定値頂点の挿入。 -/
lemma evaluateFunctorAt_as_ev (A C : SSet.{u}) (a : A _⦋0⦌) :
    lift (SSet.const a) (𝟙 ((ihom A).obj C)) ≫ (ihom.ev A).app C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a := by
  rfl

/-- 内部 uncurry 後の第二添字を固定する行制限は第二添字での評価。 -/
lemma ihomUncurry_pre_row (A B C : SSet.{u}) (b : B _⦋0⦌) :
    ihomUncurry A B C ≫ (pre (lift (𝟙 A) (SSet.const b))).app C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj C) b := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_ihomUncurry]
  have hs : (lift (𝟙 A) (SSet.const b) ▷ (ihom B).obj ((ihom A).obj C)) ≫
      (α_ A B ((ihom B).obj ((ihom A).obj C))).hom =
    A ◁ lift (SSet.const b) (𝟙 ((ihom B).obj ((ihom A).obj C))) := rfl
  rw [← Category.assoc, hs, ← MonoidalCategory.whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluateFunctorAt_as_ev]
  rfl

/-- 内部 uncurry 後の第一添字を固定する列制限は第一添字での後合成評価。 -/
lemma ihomUncurry_pre_column (A B C : SSet.{u}) (a : A _⦋0⦌) :
    ihomUncurry A B C ≫ (pre (lift (SSet.const a) (𝟙 B))).app C =
      (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_ihomUncurry]
  have hu : uncurry ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a)) =
      (ihom.ev B).app ((ihom A).obj C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a := by
    simpa only [Category.id_comp, uncurry_id_eq_ev] using
      (uncurry_natural_right (𝟙 ((ihom B).obj ((ihom A).obj C)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a))
  rw [hu]
  have hs : ((lift (SSet.const a) (𝟙 B) ▷ (ihom B).obj ((ihom A).obj C)) ≫
      (α_ A B ((ihom B).obj ((ihom A).obj C))).hom) ≫
      A ◁ (ihom.ev B).app ((ihom A).obj C) =
    (ihom.ev B).app ((ihom A).obj C) ≫ lift (SSet.const a) (𝟙 ((ihom A).obj C)) := rfl
  rw [← Category.assoc, ← Category.assoc, hs, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluateFunctorAt_as_ev]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
