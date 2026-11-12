module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PullbackSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：反復 pullback と一度の pullback の標準比較による相対切断の底変換合成則。
方針：全パラメーターの相対評価を二つの第一射影へ戻して比較する。
規約：底写像・射影に充填性は要求しない。
使われ方：P-12 の共同切断底変換の指定同型の合成を構成する入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：一度の底変換の切断を、標準比較で反復底変換の切断へ送る。
方針：標準 pullback 合成同型の逆による相対後合成を使う。
規約：同じ二つの底写像を使う。使われ方：底変換比較の合成の始点。 -/
def relativeBaseChangeCompComparison {A E B D T : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (l : T ⟶ D) (a : A ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p (l ≫ k)) a ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd (pullback.snd p k) l) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.snd p (l ≫ k))
    (pullback.snd (pullback.snd p k) l) (pullbackLeftPullbackSndIso p k l).inv
    (pullbackLeftPullbackSndIso_inv_snd_snd p k l) a

/-- 概要：元の底変換比較は標準反復 pullback 比較を介して合成を保存する。
方針：任意のパラメーターの評価を二回の第一射影へ戻す。
規約：単体ごとの存在でなく切断空間の元の写像の等式。
使われ方：指定共同切断比較の合成の成分計算。 -/
lemma relativeBaseChangeForward_comp {A E B D T : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (l : T ⟶ D) (a : A ⟶ T) :
    relativeBaseChangeCompComparison p k l a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward (pullback.snd p k) l a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k (a ≫ l) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p (l ≫ k) a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p ((a ≫ l) ≫ k)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward_uncurry]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (relativeBaseChangeCompComparison p k l a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p (l ≫ k)) a)) ≫
        (pullbackLeftPullbackSndIso p k l).inv := by
    simpa only [Category.id_comp, relativeBaseChangeCompComparison] using
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_uncurry (pullback.snd p (l ≫ k))
        (pullback.snd (pullback.snd p k) l) (pullbackLeftPullbackSndIso p k l).inv
        (pullbackLeftPullbackSndIso_inv_snd_snd p k l) a (𝟙 _))
  rw [hp, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  symm
  simpa only [Category.id_comp] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward_uncurry p (l ≫ k) a (𝟙 _))

/-- 概要：標準反復 pullback 比較による切断の写像は厳密な同型。
方針：底上の標準同型を相対後合成関手で写す。
規約：底と射影の充填性を要求しない。使われ方：共同比較成分の可逆性。 -/
def relativeBaseChangeCompIso {A E B D T : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (l : T ⟶ D) (a : A ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p (l ≫ k)) a ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd (pullback.snd p k) l) a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPostFunctor a).mapIso
    (Over.isoMk (f := Over.mk (pullback.snd p (l ≫ k)))
      (g := Over.mk (pullback.snd (pullback.snd p k) l))
      (pullbackLeftPullbackSndIso p k l).symm
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l))

/-- 概要：切断の標準比較同型の順方向は元の指定比較射。
方針：相対後合成関手の同型への作用を展開する。
規約：同じ比較を保持する。使われ方：実比較の可逆性の回収。 -/
lemma relativeBaseChangeCompIso_hom {A E B D T : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (l : T ⟶ D) (a : A ⟶ T) :
    (relativeBaseChangeCompIso p k l a).hom = relativeBaseChangeCompComparison p k l a := rfl

/-- 概要：標準切断比較は任意の標的への前合成同値。
方針：同じ射を持つ厳密な同型を使う。
規約：射影の充填性を要求しない。使われ方：共同比較の成分の同値判定。 -/
lemma relativeBaseChangeCompComparison_isPrecompositionEquivalence {A E B D T : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (l : T ⟶ D) (a : A ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (relativeBaseChangeCompComparison p k l a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (relativeBaseChangeCompIso p k l a)

/-- 概要：高次相対関手の評価は任意のパラメーター制限後も元の底図式を被覆する。
方針：頂点 fiber の条件を高次評価へ写す。
規約：射影の充填性を要求しない。使われ方：底変換の全高次自然性の第二射影。 -/
lemma relativeFunctor_projection_apply {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    {n m : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a).obj n)
    (α : n ⟶ m) (x : A.obj m) :
    p.app m (s.val.app m α x) = a.app m x := by
  exact congrArg (fun z ↦ z.app m α x) s.property

/-- 概要：元の相対後合成は底上の始域の前合成に関して自然。
方針：任意の単体とパラメーター制限で元の写像の合成を計算する。
規約：射影の充填性を要求しない。使われ方：標準切断比較の添字方向の自然性。 -/
lemma relativeFunctorPost_overPre {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    {a b : Over B} (g : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf b.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a.hom).app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p g).app n s)).val.app m α) x =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q g).app n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf b.hom).app n s)).val.app m α) x
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorOverPre_apply,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorOverPre_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_apply]

/-- 概要：標準反復 pullback 同型は全ての高次相対射の底変換に関して自然。
方針：二つの射影と元の第一射影の三座標で各単体を比較する。
規約：パラメーターの次数と評価の次数は独立。
使われ方：標準切断比較を全 left fibrations の共同比較へ束ねる。 -/
lemma iteratedPullbackInv_relativeFunctorPullback {E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) (l : T ⟶ D)
    {n m : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p).obj n)
    (α : n ⟶ m) (x : (pullback p (l ≫ k)).obj m) :
    (pullbackLeftPullbackSndIso q k l).inv.app m
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q (l ≫ k)).app n s).val.app m α x) =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback (pullback.snd p k) (pullback.snd q k) l).app n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p q k).app n s)).val.app m α
          ((pullbackLeftPullbackSndIso p k l).inv.app m x)) := by
  rcases m with ⟨⟨m⟩⟩
  have hc_fst {Z : SSet.{u}} (r : Z ⟶ B) (z : (pullback r (l ≫ k)) _⦋m⦌) :
      (pullback.fst r k).app _ ((pullback.fst (pullback.snd r k) l).app _
        ((pullbackLeftPullbackSndIso r k l).inv.app _ z)) =
      (pullback.fst r (l ≫ k)).app _ z :=
    congrArg (fun f : pullback r (l ≫ k) ⟶ Z ↦ f.app _ z)
      (pullbackLeftPullbackSndIso_inv_fst r k l)
  have hc_mid {Z : SSet.{u}} (r : Z ⟶ B) (z : (pullback r (l ≫ k)) _⦋m⦌) :
      (pullback.snd r k).app _ ((pullback.fst (pullback.snd r k) l).app _
        ((pullbackLeftPullbackSndIso r k l).inv.app _ z)) =
      l.app _ ((pullback.snd r (l ≫ k)).app _ z) :=
    congrArg (fun f : pullback r (l ≫ k) ⟶ D ↦ f.app _ z)
      (pullbackLeftPullbackSndIso_inv_fst_snd r k l)
  have hc_snd {Z : SSet.{u}} (r : Z ⟶ B) (z : (pullback r (l ≫ k)) _⦋m⦌) :
      (pullback.snd (pullback.snd r k) l).app _
        ((pullbackLeftPullbackSndIso r k l).inv.app _ z) =
      (pullback.snd r (l ≫ k)).app _ z :=
    congrArg (fun f : pullback r (l ≫ k) ⟶ T ↦ f.app _ z)
      (pullbackLeftPullbackSndIso_inv_snd_snd r k l)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext (pullback.snd q k) l
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext q k
    · rw [hc_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_apply_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_apply_fst,
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_apply_fst, hc_fst]
    · rw [hc_mid, relativeFunctor_projection_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPullback_apply_fst,
        relativeFunctor_projection_apply, hc_mid]
  · rw [hc_snd, relativeFunctor_projection_apply, relativeFunctor_projection_apply, hc_snd]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
