module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRestrictionLaws
public import SerrePositivity.InfinityCategories.F2.Ind.FullPosetSubsetCoconeLift

/-!
概要：二段の形状制限に沿う指定全余錐の厳密な持ち上げを接続する。
方針：元の指定余錐を合成則で読み替え、順に持ち上げて全射の等号を回収する。
規約：元の試験族と指定余錐を保持する。
使われ方：極大点追加後も固定下方部分の指定余錐を保つ帰納段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：二つの厳密な指定余錐持ち上げは、元の合成形状制限でも成立する。
方針：指定余錐の二段持ち上げ。規約：全射の等号。使われ方：下方部分固定の帰納。 -/
lemma exists_diagramComma_cocone_lift_comp (κ : Cardinal.{u})
    {I J K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (f : J ⟶ K) (g : I ⟶ J) {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
    (hf : ∀ c₁ : JoinCocone (q ≫ diagramCommaRestriction κ D f),
      ∃ c : JoinCocone q, mapJoinCocone (diagramCommaRestriction κ D f) c = c₁)
    (hg : ∀ G : JoinCocone ((q ≫ diagramCommaRestriction κ D f) ≫
        diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g),
      ∃ c₁ : JoinCocone (q ≫ diagramCommaRestriction κ D f),
        mapJoinCocone
          (diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g) c₁ = G)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (g ≫ f))) :
    ∃ c : JoinCocone q,
      mapJoinCocone (diagramCommaRestriction κ D (g ≫ f)) c = G := by
  let G' : JoinCocone ((q ≫ diagramCommaRestriction κ D f) ≫
      diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g) :=
    ⟨G.val, by rw [Category.assoc, diagramCommaRestriction_comp]; exact G.property⟩
  obtain ⟨c₁, hc₁⟩ := hg G'
  obtain ⟨c, hc⟩ := hf c₁
  refine ⟨c, Subtype.ext ?_⟩
  change c.val ≫ diagramCommaRestriction κ D (g ≫ f) = G.val
  have h₁ := congrArg Subtype.val hc
  have h₂ := congrArg Subtype.val hc₁
  change c.val ≫ diagramCommaRestriction κ D f = c₁.val at h₁
  calc
    _ = c.val ≫ (diagramCommaRestriction κ D f ≫
        diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g) :=
      congrArg (fun r ↦ c.val ≫ r) (diagramCommaRestriction_comp κ D f g).symm
    _ = (c.val ≫ diagramCommaRestriction κ D f) ≫
        diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g :=
      (Category.assoc _ _ _).symm
    _ = c₁.val ≫
        diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) g :=
      congrArg (fun r ↦ r ≫ _) h₁
    _ = G.val := h₂

end SerrePositivity.InfinityCategories.F2.Ind
