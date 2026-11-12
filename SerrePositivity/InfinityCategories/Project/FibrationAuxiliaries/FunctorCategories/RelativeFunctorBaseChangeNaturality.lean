module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition

/-!
概要：相対関手空間の底変換同型と前合成の全パラメーターでの自然性。
方針：相対 uncurry の計算則を内部 Hom の包含と任意の単体の評価へ移す。
規約：射影の充填性や底の quasicategory 性は不要。
使われ方：引き戻しの strict transport を共同切断図式と豊穣自然に比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：底変換の順方向を内部 Hom に含めると第一射影の後合成になる。
方針：相対 uncurry の底変換の公式を内部 Hom の単射性で使う。
規約：任意の相対関手空間に対する射の等式。
使われ方：底変換の同型の自然性の計算。 -/
lemma relativeFunctorBaseChangeForward_ι {A E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (a : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ k)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map (pullback.snd p k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫
      (ihom A).map (pullback.fst p k) := by
  apply uncurry_injective
  rw [uncurry_natural_right]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward_uncurry p k a (𝟙 _)
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry] using h

/-- 概要：相対写像空間の引き戻しは第一射影の後で元の族の前合成になる。
方針：相対 uncurry の二射影の公式を内部 Hom へ戻す。
規約：全高次の相対射の空間全体での等式。
使われ方：底変換した高次の後合成と評価の比較。 -/
lemma relativeFunctorPullback_ι_fst {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (pullback p k)).map (pullback.snd q k))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (pullback.snd p k)) ≫
      (ihom (pullback p k)).map (pullback.fst q k) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom E).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫
      (pre (pullback.fst p k)).app F := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_natural_right, uncurry_pre_app]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback_uncurry_fst p q k (𝟙 _)
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry] using h

/-- 概要：底変換の順方向は任意のパラメーター単体で第一射影の後合成。
方針：内部 Hom の包含の公式を高次の評価で計算する。
規約：パラメーターの次数と評価の次数は独立。
使われ方：相対合成の底変換の豊穣自然性。 -/
lemma relativeFunctorBaseChangeForward_apply {A E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (a : A ⟶ D)
    {n m : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p k) a).obj n)
    (α : n ⟶ m) (x : A.obj m) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k a).app n s).val.app m α) x =
      (pullback.fst p k).app m (s.val.app m α x) := by
  have h := congrArg (fun f ↦ ((f.app n s).app m α) x)
    (relativeFunctorBaseChangeForward_ι p k a)
  exact h

/-- 概要：引き戻した高次の相対射の第一射影は元の族の第一射影での評価。
方針：内部 Hom の前後合成の公式を任意の単体で評価する。
規約：全てのパラメーター制限を保つ。
使われ方：底変換の後合成への自然性。 -/
lemma relativeFunctorPullback_apply_fst {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    {n m : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p).obj n)
    (α : n ⟶ m) (x : (pullback p k).obj m) :
    (pullback.fst q k).app m
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k).app n s).val.app m α x) =
      s.val.app m α ((pullback.fst p k).app m x) := by
  have h := congrArg (fun f ↦ ((f.app n s).app m α) x)
    (relativeFunctorPullback_ι_fst p q k)
  change (pullback.fst q k).app m
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k).app n s).val.app m (α ≫ 𝟙 m) x) =
    s.val.app m (α ≫ 𝟙 m) ((pullback.fst p k).app m x) at h
  simpa only [Category.comp_id] using h

/-- 概要：底変換の順方向は底上の定義域の前合成と厳密に可換。
方針：内部 Hom の包含後に前合成と第一射影の後合成を交換する。
規約：元の図式の全ての射について成立。
使われ方：底変換の比較を添字図式全体へ束ねる。 -/
lemma relativeFunctorBaseChangeForward_overPre {E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) {a b : Over D} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre (pullback.snd p k) f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k a.hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k b.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p ((Over.map k).map f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom a.left).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a.hom ≫ k))
  rw [Category.assoc, relativeFunctorBaseChangeForward_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_ι, Category.assoc, ← (pre f.left).naturality]
  rw [← Category.assoc, ← relativeFunctorBaseChangeForward_ι]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k b.hom ≫ t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_ι p ((Over.map k).map f)).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
