module

public import SerrePositivity.InfinityCategories.F1B.Cofinality
public import SerrePositivity.InfinityCategories.F1B.RightAnodyneTensor

/-!
概要：right fibration への相対関手空間と right anodyne な制限。
方針：内部 Hom の頂点 fiber の Kan 性と、相対内部 Hom の全境界充填を使う。
規約：元の底上の射を使い、straightening や相対関手空間の別模型を import しない。
使われ方：Kerodon Definition 7.2.1.1、Proposition 7.2.1.3 の right 側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：right fibration への相対関手空間は Kan 複体。
方針：後合成の内部 Hom の right fibration 性と指定頂点 fiber の Kan 性を使う。
規約：底図式と底の quasicategory 性は不要。
使われ方：Kerodon Definition 7.2.1.1 の Kan 複体間の検査。 -/
instance cofinalFunctorSpace_right_kanComplex {A E B : SSet.{u}} (p : E ⟶ B)
    [RightFibration p] (a : A ⟶ B) : KanComplex (cofinalFunctorSpace p a) :=
  vertexFiber_kanComplex ((ihom A).map p) (functorVertex a)

/-- 概要：right anodyne な射による相対前合成は trivial Kan fibration。
方針：底を固定した持ち上げ問題を相対内部 Hom に入れて解き、再び fiber へ戻す。
規約：元の射 p の right fibration 性だけを要求する。
使われ方：Kerodon §5.3.1、終対象の nerve の頂点包含に沿う制限。 -/
lemma cofinalFunctorPre_trivialKanFibration_of_rightAnodyne {A D E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : rightAnodyneExtensions i) : TrivialKanFibration (cofinalFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := cofinalTrivialKanFibration_relativeHom_of_rightAnodyne i hi p sq'
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  have := TrivialKanFibration.mem (p := sq'.π) (boundary n).ι inferInstance
  constructor
  intro u v sq
  let ιA := vertexFiberι ((ihom A).map p) (functorVertex a)
  let ιD := vertexFiberι ((ihom D).map p) (functorVertex (i ≫ a))
  let V : (Δ[n] : SSet.{u}) ⟶ sq'.pt :=
    sq'.isPullback.lift (v ≫ ιD) (SSet.const (functorVertex a)) (by
      change (v ≫ vertexFiberι ((ihom D).map p) (functorVertex (i ≫ a))) ≫
        (ihom D).map p = SSet.const (functorVertex a) ≫ (pre i).app B
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
      rfl)
  have hVfst : V ≫ sq'.fst = v ≫ ιD := sq'.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ sq'.snd = SSet.const (functorVertex a) := sq'.isPullback.lift_snd _ _ _
  have hs : CommSq (u ≫ ιA) (boundary n).ι sq'.π V := by
    constructor
    apply sq'.hom_ext
    · simp only [Category.assoc, sq'.π_fst, hVfst]
      change (u ≫ ιA) ≫ (pre i).app E = ((boundary n).ι ≫ v) ≫ ιD
      exact (congrArg (fun q ↦ q ≫ ιD) sq.w).trans (by rfl)
    · simp only [Category.assoc, sq'.π_snd, hVsnd]
      change (u ≫ vertexFiberι ((ihom A).map p) (functorVertex a)) ≫ (ihom A).map p = _
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  have hbase : hs.lift ≫ (ihom A).map p = SSet.const (functorVertex a) := by
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.snd := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_snd.symm
      _ = V ≫ sq'.snd := congrArg (fun q ↦ q ≫ sq'.snd) hs.fac_right
      _ = _ := hVsnd
  let W := vertexFiberLift ((ihom A).map p) (functorVertex a) hs.lift hbase
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply vertexFiber_hom_ext ((ihom A).map p) (functorVertex a)
    change ((boundary n).ι ≫ W) ≫ ιA = u ≫ ιA
    rw [Category.assoc, vertexFiberLift_ι]
    exact hs.fac_left
  · apply vertexFiber_hom_ext ((ihom D).map p) (functorVertex (i ≫ a))
    rw [Category.assoc, cofinalFunctorPre_ι, ← Category.assoc, vertexFiberLift_ι]
    change hs.lift ≫ (pre i).app E = v ≫ ιD
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.fst := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_fst.symm
      _ = V ≫ sq'.fst := congrArg (fun q ↦ q ≫ sq'.fst) hs.fac_right
      _ = _ := hVfst

/-- 概要：right anodyne に沿う任意の底図式の制限はホモトピー同値。
方針：相対関手空間間の trivial Kan fibration から同じ射のホモトピー逆を得る。
規約：p は right fibration、底図式 a は任意。
使われ方：Kerodon Proposition 7.2.1.3 の十分性。 -/
lemma cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_rightAnodyne
    {A D E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : rightAnodyneExtensions i) :
    IsSimplicialHomotopyEquivalence (cofinalFunctorPre p a i) := by
  have := cofinalFunctorPre_trivialKanFibration_of_rightAnodyne p a i hi
  exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

/-- 概要：right anodyne な射は right cofinal。
方針：任意の right fibration について、恒等底図式の制限のホモトピー逆を取る。
規約：底の quasicategory 性や別途の単射性の仮定は不要。
使われ方：Kerodon Proposition 7.2.1.3 の十分性。 -/
lemma isRightCofinal_of_rightAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : rightAnodyneExtensions i) : IsRightCofinal i := by
  intro E p hp
  exact cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_rightAnodyne p (𝟙 B) i hi

end SerrePositivity.InfinityCategories
