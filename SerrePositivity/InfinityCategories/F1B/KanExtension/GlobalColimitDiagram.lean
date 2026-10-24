module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalColimitFamily
public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalDiagramFamilyEquiv

/-!
概要：全空間の一つの図式の fiber ごとの余極限から相対 join 上の図式を構成する。
方針：相対始対象の族を実際の図式へ戻し、左端の制限の等式を回収する。
規約：各 fiber の指定図式だけの余極限の存在を仮定する。
使われ方：oriented comma に沿う Kan 拡張の coherent な組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定図式の fiber ごとの余極限から相対 join の普遍な図式へ厳密に延長できる。
方針：普遍余錐の族を選び、恒等射上の族と図式の全単射の逆で戻す。
規約：元の図式を左包含への制限として保つ。
使われ方：点ごとの余極限から左 Kan 拡張を構成する主経路。 -/
lemma exists_kanGlobalColimit_diagram {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (F : K ⟶ D) (hcol : ∀ c : C _⦋0⦌, HasColimit (vertexFiberι p c ≫ F)) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧
        ∀ c : C _⦋0⦌, InitialBoundaryLifting
          (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
            ((kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
              (Opposite.op ⦋0⦌) c) := by
  obtain ⟨l, hl, hli⟩ := exists_kanGlobalColimit_initial_family p F hcol
  have hlp : l ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D = 𝟙 C := by
    change l ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection
      (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom D = 𝟙 C
    rw [← SerrePositivity.InfinityCategories.fiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p),
      ← Category.assoc, hl]
    exact kanGlobalDiagramFamily_projection p F
  let H := (kanGlobalDiagramFamilyEquiv (D := D)
    (relativeJoinBaseProjection p (𝟙 C))).symm ⟨l, hlp⟩
  have hH : kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H = l :=
    congrArg Subtype.val ((kanGlobalDiagramFamilyEquiv (D := D)
      (relativeJoinBaseProjection p (𝟙 C))).apply_symm_apply ⟨l, hlp⟩)
  refine ⟨H, ?_, ?_⟩
  · apply kanGlobalDiagramFamily_injective p
    erw [← kanGlobalDiagramFamily_pre (kanRelativeJoinInlOver p) H, hH]
    exact hl
  · rw [hH]
    exact hli

end SerrePositivity.InfinityCategories.F1B
