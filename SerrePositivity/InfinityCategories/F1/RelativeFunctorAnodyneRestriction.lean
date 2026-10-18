module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.LeftAnodynePushoutProduct

/-!
概要：left anodyne な始域の制限による相対関手空間の全境界持ち上げ。
方針：相対内部 Hom の持ち上げを、固定した底の図式の fiber に制限する。
規約：p は left fibration、底の単体集合に quasicategory 性は不要。
使われ方：Kerodon §5.3.1、strict transport の始対象における評価の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：left anodyne な射による相対前合成は trivial Kan fibration。
方針：底を固定した持ち上げ問題を相対内部 Hom に入れて解き、再び fiber へ戻す。
規約：元の射 p の left fibration 性だけを要求する。
使われ方：Kerodon §5.3.1、始対象の nerve の頂点包含に沿う制限。 -/
lemma relativeFunctorPre_trivialKanFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) : TrivialKanFibration (relativeFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := trivialKanFibration_relativeHom_of_leftAnodyne i hi p sq'
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
    rw [Category.assoc, relativeFunctorPre_ι, ← Category.assoc, vertexFiberLift_ι]
    change hs.lift ≫ (pre i).app E = v ≫ ιD
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.fst := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_fst.symm
      _ = V ≫ sq'.fst := congrArg (fun q ↦ q ≫ sq'.fst) hs.fac_right
      _ = _ := hVfst

end SerrePositivity.InfinityCategories
