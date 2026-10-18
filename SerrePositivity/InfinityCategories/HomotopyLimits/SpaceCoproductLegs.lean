module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCoconeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceCoproducts

/-!
概要：空間の実際の余積余錐の各脚は直和の元の成分包含である。
方針：既存の図式へ移送した余錐の脚を strict な余錐の脚へ戻し、一般の脚の照合を使う。
規約：同値類でなく標準区間から coherent nerve への射の等号。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、F2 の 𝒮 の余積の包含射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {J : Type u}

/-- 概要：空間の実際の余積余錐の成分 j の脚。
方針：元の離散図式の標準頂点で native な余錐の脚を取る。
規約：添字は J の元で、図式の宇宙の持ち上げを明示する。
使われ方：Kerodon 7.5.4.6、𝒮 の実際の余積への包含。 -/
noncomputable def spaceCoproductCoconeLeg (F : Discrete J ⥤ KanObject.{u}) (j : J) :
    (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  coherentCoconeLegMap (spaceCoproductCocone F)
    (SSet.yonedaEquiv.symm (ULift.up (nerveVertex (Discrete.mk j))))

/-- 概要：空間の実際の余積余錐の脚は成分添字を付ける元の包含射の coherent 表示。
方針：図式の移送が脚を変えないことと一般の strict な余錐の脚の等式を使う。
規約：余積対象は実際の直和で、元の包含射に一致する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、F2 の余積の射の同定。 -/
lemma spaceCoproductCoconeLeg_eq (F : Discrete J ⥤ KanObject.{u}) (j : J) :
    spaceCoproductCoconeLeg F j = SSet.yonedaEquiv.symm
      ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj ⟨j⟩ ⟶ kanCoproductObject F from
          simplicialCoproductι (fun k : J ↦ (F.obj ⟨k⟩).obj) j))) := by
  unfold spaceCoproductCoconeLeg spaceCoproductCocone
  rw [coherentCoconeLegMap_ofDiagramEq]
  exact strictNativeCoconeLeg_eq (kanCoproductCocone F) ⟨j⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
