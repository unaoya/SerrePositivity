module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyTensorLift

/-!
概要：直積の錐族の lift の成分と一意性。
方針：fiber の包含後に内部 Hom の直積の二成分を計算する。
規約：元の図式と全パラメータの族を保持する。
使われ方：錐族の直積比較同型の往復。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {J X Y T : SSet.{u}} (r : J ⟶ X ⊗ Y)
variable (a : T ⟶ coneFamily (r ≫ fst X Y)) (b : T ⟶ coneFamily (r ≫ snd X Y))

/-- 概要：直積の錐族への lift の第一成分は元の族。
方針：包含後に内部 Hom の第一成分を計算する。
規約：図式固定の錐族内の射の等式。
使われ方：直積の比較同型の第一射影。 -/
lemma coneFamilyTensorLift_fst :
    coneFamilyTensorLift r a b ≫ coneFamilyPostcomp r (fst X Y) = a := by
  apply vertexFiber_hom_ext (coneRestriction J X) (functorVertex (r ≫ fst X Y))
  rw [Category.assoc, coneFamilyPostcomp_ι, ← Category.assoc]
  change (vertexFiberLift _ _ _ _ ≫ vertexFiberι _ _) ≫ _ = _
  rw [vertexFiberLift_ι]
  exact internalHomTensorLift_fst ..

/-- 概要：直積の錐族への lift の第二成分は元の族。
方針：包含後に内部 Hom の第二成分を計算する。
規約：図式固定の錐族内の射の等式。
使われ方：直積の比較同型の第二射影。 -/
lemma coneFamilyTensorLift_snd :
    coneFamilyTensorLift r a b ≫ coneFamilyPostcomp r (snd X Y) = b := by
  apply vertexFiber_hom_ext (coneRestriction J Y) (functorVertex (r ≫ snd X Y))
  rw [Category.assoc, coneFamilyPostcomp_ι, ← Category.assoc]
  change (vertexFiberLift _ _ _ _ ≫ vertexFiberι _ _) ≫ _ = _
  rw [vertexFiberLift_ι]
  exact internalHomTensorLift_snd ..

/-- 概要：直積の錐族への射は二成分で決まる。
方針：包含後に内部 Hom の射の外延性を使う。
規約：始域のパラメータは任意。
使われ方：錐族の比較同型の逆条件。 -/
lemma coneFamilyTensor_hom_ext {f g : T ⟶ coneFamily r}
    (hx : f ≫ coneFamilyPostcomp r (fst X Y) = g ≫ coneFamilyPostcomp r (fst X Y))
    (hy : f ≫ coneFamilyPostcomp r (snd X Y) = g ≫ coneFamilyPostcomp r (snd X Y)) :
    f = g := by
  apply vertexFiber_hom_ext (coneRestriction J (X ⊗ Y)) (functorVertex r)
  apply internalHomTensor_hom_ext
  · simpa only [Category.assoc, coneFamilyPostcomp_ι] using congrArg
      (fun f ↦ f ≫ vertexFiberι (coneRestriction J X) (functorVertex (r ≫ fst X Y))) hx
  · simpa only [Category.assoc, coneFamilyPostcomp_ι] using congrArg
      (fun f ↦ f ≫ vertexFiberι (coneRestriction J Y) (functorVertex (r ≫ snd X Y))) hy

end SerrePositivity.InfinityCategories.F2
