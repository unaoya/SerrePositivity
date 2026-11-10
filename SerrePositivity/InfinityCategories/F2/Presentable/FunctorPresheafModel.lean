module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafPresentable
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableEquivalence
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects

/-!
概要：小さい圏上の前層への関手圏を、積の底上の前層圏として表示する。
方針：内部 Hom の curry 同型と指定宇宙変更の積同型を合成する。
規約：底 K と A は宇宙 u、全関手圏は u+1。
使われ方：Fun(K,C) の反映模型の元となる presentable な前層圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の二底の積の反転と二重反転を、指定宇宙変更の積へ比較する。
方針：反転の積との厳密な整合性と二重反転同型を使う。
規約：curry で使う因子順は A の反対、K の順。
使われ方：関手前層模型の始域の同型。 -/
def functorPresheafBaseIso (K A : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ K.op).op ≅
      (SSet.uliftFunctor.{u + 1, u}).obj A.op ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj K :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso
    ((show (A ⊗ K.op).op ≅ A.op ⊗ K.op.op from Iso.refl _) ≪≫
      ((Iso.refl A.op) ⊗ᵢ (SSet.opFunctorCompOpFunctorIso.app K))) ≪≫ uliftTensorIso A.op K

/-- 概要：小さい底 K 上の前層値全関手圏は積の底上の元の前層圏と同型。
方針：同じ指定内部 Hom の curry 同型を底の比較と合成する。
規約：全自然変換と全高次単体を保持する。
使われ方：前層値関手圏の presentable 性。 -/
def functorPresheafIso (K A : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (PresheafInfinity A) ≅
      PresheafInfinity (A ⊗ K.op) :=
  (ihomCurryIso ((SSet.uliftFunctor.{u + 1, u}).obj A.op)
    ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity).symm ≪≫
      (internalHom.mapIso (functorPresheafBaseIso K A).op).app SpaceInfinity

/-- 概要：小さい quasicategory 上の前層値関手圏は presentable。
方針：積の底上の前層模型から全同型で輸送する。
規約：随伴関手定理や新しい局所化の存在は使わない。
使われ方：一般の presentable 圏への関手圏の反映模型。 -/
lemma functorPresheaf_isPresentable (K A : SSet.{u}) [Quasicategory K] [Quasicategory A] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (PresheafInfinity A)) := by
  have : Quasicategory (A ⊗ K.op) := F2.quasicategory_tensor A K.op
  exact (presheaf_isPresentable (A ⊗ K.op)).of_equivalence
    (qCatEquivalenceOfIso (functorPresheafIso K A).symm)

end SerrePositivity.InfinityCategories.F2.Presentable
