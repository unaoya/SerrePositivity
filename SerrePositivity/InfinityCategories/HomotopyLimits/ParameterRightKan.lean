module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTerminalHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightKanAdjunctComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorHomUncurry
public import SerrePositivity.InfinityCategories.Core.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRightHom

/-!
概要：任意の直積パラメータの標準右 Kan Hom 比較と端点の輸送を照合する。
方針：標準 Hom の式と、相対境界充填の判定を使用する。
規約：元の対象・射・端点の同一視を保持する。使われ方：一般 coherent 極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 内部 uncurry は、元の添字の制限と厳密に可換である。 -/
lemma ihomUncurry_precomp {K L A X : SSet.{u}} (δ : K ⟶ L) :
    (ihom A).map ((pre δ).app X) ≫ (ihomCurryIso K A X).inv =
      (ihomCurryIso L A X).inv ≫ (pre (δ ▷ A)).app X := by
  rfl

/-- 指定相対終点から、任意パラメータの恒等変換の右 Kan Hom 普遍性を得る。 -/
lemma parameterRightKanIdentity_of_terminalBoundary {K L Y : SSet.{u}}
    [Quasicategory Y] (δ : K ⟶ L) (H : L ⟶ Y)
    (hc : TerminalBoundaryLifting ((pre δ).app Y) (functorVertex H)) (B : SSet.{u}) :
    RightKanHomUniversal
      (F := uncurry (SSet.const (functorVertex H) : B ⟶ (ihom L).obj Y))
      (F₀ := (δ ▷ B) ≫ uncurry (SSet.const (functorVertex H) : B ⟶ (ihom L).obj Y))
      (δ ▷ B) (𝟙 (HomotopyCategory.mk (functorVertex
        ((δ ▷ B) ≫ uncurry (SSet.const (functorVertex H) : B ⟶ (ihom L).obj Y))))) := by
  let C : B ⟶ (ihom L).obj Y := SSet.const (functorVertex H)
  have hB := terminalBoundaryLifting_ihom_of_pointwise ((pre δ).app Y) C (by
    intro b
    change TerminalBoundaryLifting ((pre δ).app Y) (PinchedHom.constant (functorVertex H) 0)
    rw [pinchedConstant_zero]
    exact hc)
  have hw := hB.map_iso (ihomCurryIso L B Y).symm (ihomCurryIso K B Y).symm
    (ihomUncurry_precomp (A := B) (X := Y) δ).symm
  change TerminalBoundaryLifting ((pre (δ ▷ B)).app Y)
    ((ihomCurryIso L B Y).inv.app (Opposite.op ⦋0⦌) (functorVertex C)) at hw
  rw [ihomUncurry_functorVertex] at hw
  intro T
  have hm := homMap_bijective_of_terminalBoundaryLifting ((pre (δ ▷ B)).app Y)
    (functorVertex (uncurry C)) hw (functorVertex T)
  have he : rightKanHomMap (F := uncurry C) (F₀ := (δ ▷ B) ≫ uncurry C) (δ ▷ B)
      (𝟙 (HomotopyCategory.mk (functorVertex ((δ ▷ B) ≫ uncurry C)))) T =
      ((hoFunctor.map ((pre (δ ▷ B)).app Y)).toFunctor.map :
        FunctorHom T (uncurry C) → FunctorHom ((δ ▷ B) ≫ T) ((δ ▷ B) ≫ uncurry C)) := by
    funext α
    exact Category.comp_id _
  rw [he]
  exact hm

/-- 元の恒等変換の右 Kan Hom 普遍性は同じ標準単位の右随伴で保たれる。 -/
lemma rightKanIdentity_postcomp {K C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ C)
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitMappingSpaceCondition η) (H : C ⟶ Y)
    (h : RightKanHomUniversal (F := H) (F₀ := δ ≫ H) δ
      (𝟙 (HomotopyCategory.mk (functorVertex (δ ≫ H))))) :
    RightKanHomUniversal (F := H ≫ G) (F₀ := δ ≫ (H ≫ G)) δ
      (𝟙 (HomotopyCategory.mk (functorVertex (δ ≫ (H ≫ G))))) := by
  have ht := rightKanHomUniversal_postcomp_of_unitCondition δ η hη
    (H := H) (d := δ ≫ H) (𝟙 (HomotopyCategory.mk (functorVertex (δ ≫ H)))) h
  simp only [CategoryTheory.Functor.map_id] at ht
  change RightKanHomUniversal (F := H ≫ G) (F₀ := δ ≫ (H ≫ G)) δ
    (𝟙 (HomotopyCategory.mk (functorVertex (δ ≫ (H ≫ G))))) at ht
  exact ht

/-- 元の二胞体の制限と uncurry は、両端の等式による輸送の下で可換である。 -/
lemma functorHomUncurry_precomp {K L A X : SSet.{u}} [Quasicategory X]
    (δ : K ⟶ L) {U V : A ⟶ (ihom L).obj X} (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (uncurry_pre_app X U δ) (uncurry_pre_app X V δ)
      (functorHomUncurry (K := K) (A := A) (X := X)
        (U := U ≫ (pre δ).app X) (V := V ≫ (pre δ).app X)
        (show FunctorHom (U ≫ (pre δ).app X) (V ≫ (pre δ).app X) from
          (hoFunctor.map ((ihom A).map ((pre δ).app X))).toFunctor.map
            (X := HomotopyCategory.mk (functorVertex U))
            (Y := HomotopyCategory.mk (functorVertex V)) α)) =
    (hoFunctor.map ((pre (δ ▷ A)).app X)).toFunctor.map
      (functorHomUncurry (K := L) (A := A) (X := X) (U := U) (V := V) α) := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ α
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  apply homMk_transport (congrArg functorVertex (uncurry_pre_app X U δ))
    (congrArg functorVertex (uncurry_pre_app X V δ))
  change ((ihom A).map ((pre δ).app X) ≫ (ihomCurryIso K A X).inv).app
      (Opposite.op ⦋1⦌) e.edge =
    ((ihomCurryIso L A X).inv ≫ (pre (δ ▷ A)).app X).app (Opposite.op ⦋1⦌) e.edge
  rw [ihomUncurry_precomp]

/-- 全パラメータの右 Kan 普遍性から、定値族の標準制限 Hom の全単射を回収する。 -/
lemma constantHom_precomp_bijective_of_parameterRightKan {K L X : SSet.{u}}
    [Quasicategory X] (δ : K ⟶ L) (H : L ⟶ X)
    (h : ∀ (A : SSet.{u}) [Quasicategory A], RightKanHomUniversal
      (F := uncurry (SSet.const (functorVertex H) : A ⟶ (ihom L).obj X))
      (F₀ := (δ ▷ A) ≫ uncurry (SSet.const (functorVertex H) : A ⟶ (ihom L).obj X))
      (δ ▷ A) (𝟙 (HomotopyCategory.mk (functorVertex
        ((δ ▷ A) ≫ uncurry (SSet.const (functorVertex H) : A ⟶ (ihom L).obj X))))))
    (A : SSet.{u}) [Quasicategory A] (T : L ⟶ X) :
    Function.Bijective (SerrePositivity.InfinityCategories.F1B.constantHomPostcomp ((pre δ).app X) A
      (functorVertex T) (functorVertex H)) := by
  let U : A ⟶ (ihom L).obj X := SSet.const (functorVertex T)
  let V : A ⟶ (ihom L).obj X := SSet.const (functorVertex H)
  let q := (pre δ).app X
  have hs := functorHomUncurry_bijective (K := L) (A := A) (X := X) U V
  have ht := functorHomUncurry_bijective (K := K) (A := A) (X := X) (U ≫ q) (V ≫ q)
  let E := F1B.kanFunctorHomCongr (uncurry_pre_app X U δ) (uncurry_pre_app X V δ)
  have ht' := E.bijective.comp ht
  have hb := h A (uncurry U)
  have he : rightKanHomMap (F := uncurry V) (F₀ := (δ ▷ A) ≫ uncurry V) (δ ▷ A)
      (𝟙 (HomotopyCategory.mk (functorVertex ((δ ▷ A) ≫ uncurry V)))) (uncurry U) =
      ((hoFunctor.map ((pre (δ ▷ A)).app X)).toFunctor.map :
        FunctorHom (uncurry U) (uncurry V) →
          FunctorHom ((δ ▷ A) ≫ uncurry U) ((δ ▷ A) ≫ uncurry V)) := by
    funext α
    exact Category.comp_id _
  rw [he] at hb
  have hm : Function.Bijective
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map :
        FunctorHom U V → FunctorHom (U ≫ q) (V ≫ q)) := by
    constructor
    · intro α β heq
      apply hs.injective
      apply hb.injective
      rw [← functorHomUncurry_precomp δ α, ← functorHomUncurry_precomp δ β, heq]
    · intro β
      obtain ⟨αu, hαu⟩ := hb.surjective (E (functorHomUncurry (K := K) (A := A) (X := X)
        (U := U ≫ q) (V := V ≫ q) β))
      obtain ⟨α', rfl⟩ := hs.surjective αu
      refine ⟨α', ht'.injective ?_⟩
      change E (functorHomUncurry _) = E (functorHomUncurry β)
      dsimp only [E]
      rw [functorHomUncurry_precomp]
      exact hαu
  exact (Iso.homCongr (constantFunctorCompIso A (functorVertex T) q)
    (constantFunctorCompIso A (functorVertex H) q)).bijective.comp hm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
