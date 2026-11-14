module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeTerminalHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RightKanAdjunctComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorHomUncurry
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 内部 uncurry は、元の添字の制限と厳密に可換である。 -/
lemma ihomUncurry_precomp {K L A X : SSet.{u}} (δ : K ⟶ L) :
    (ihom A).map ((pre δ).app X) ≫ (ihomCurryIso K A X).inv =
      (ihomCurryIso L A X).inv ≫ (pre (δ ▷ A)).app X := by
  rfl

/-- 指定相対終点から、任意パラメータの恒等変換の右 Kan Hom 普遍性を得る。 -/
lemma parameterRightKanIdentity_of_terminalBoundary {K L Y : SSet.{u}}
    [Quasicategory Y] (δ : K ⟶ L) (H : L ⟶ Y)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre δ).app Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal
      (F := uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : B ⟶ (ihom L).obj Y))
      (F₀ := (δ ▷ B) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : B ⟶ (ihom L).obj Y))
      (δ ▷ B) (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        ((δ ▷ B) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : B ⟶ (ihom L).obj Y))))) := by
  let C : B ⟶ (ihom L).obj Y := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)
  have hB := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_ihom_of_pointwise ((pre δ).app Y) C (by
    intro b
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre δ).app Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact hc)
  have hw := hB.map_iso (ihomCurryIso L B Y).symm (ihomCurryIso K B Y).symm
    (ihomUncurry_precomp (A := B) (X := Y) δ).symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre (δ ▷ B)).app Y)
    ((ihomCurryIso L B Y).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex C)) at hw
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ihomUncurry_functorVertex] at hw
  intro T
  have hm := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homMap_bijective_of_terminalBoundaryLifting ((pre (δ ▷ B)).app Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry C)) hw (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F := uncurry C) (F₀ := (δ ▷ B) ≫ uncurry C) (δ ▷ B)
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((δ ▷ B) ≫ uncurry C)))) T =
      ((hoFunctor.map ((pre (δ ▷ B)).app Y)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom T (uncurry C) → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((δ ▷ B) ≫ T) ((δ ▷ B) ≫ uncurry C)) := by
    funext α
    exact Category.comp_id _
  rw [he]
  exact hm

/-- 元の恒等変換の右 Kan Hom 普遍性は同じ標準単位の右随伴で保たれる。 -/
lemma rightKanIdentity_postcomp {K C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ C)
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (H : C ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal (F := H) (F₀ := δ ≫ H) δ
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ H))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal (F := H ≫ G) (F₀ := δ ≫ (H ≫ G)) δ
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ (H ≫ G))))) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanHomUniversal_postcomp_of_unitCondition δ η hη
    (H := H) (d := δ ≫ H) (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ H)))) h
  simp only [CategoryTheory.Functor.map_id] at ht
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal (F := H ≫ G) (F₀ := δ ≫ (H ≫ G)) δ
    (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ (H ≫ G))))) at ht
  exact ht

/-- 元の二胞体の制限と uncurry は、両端の等式による輸送の下で可換である。 -/
lemma functorHomUncurry_precomp {K L A X : SSet.{u}} [Quasicategory X]
    (δ : K ⟶ L) {U V : A ⟶ (ihom L).obj X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (uncurry_pre_app X U δ) (uncurry_pre_app X V δ)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := X)
        (U := U ≫ (pre δ).app X) (V := V ≫ (pre δ).app X)
        (show _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre δ).app X) (V ≫ (pre δ).app X) from
          (hoFunctor.map ((ihom A).map ((pre δ).app X))).toFunctor.map
            (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
            (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) α)) =
    (hoFunctor.map ((pre (δ ▷ A)).app X)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := L) (A := A) (X := X) (U := U) (V := V) α) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ α
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry_pre_app X U δ))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry_pre_app X V δ))
  change ((ihom A).map ((pre δ).app X) ≫ (ihomCurryIso K A X).inv).app
      (Opposite.op ⦋1⦌) e.edge =
    ((ihomCurryIso L A X).inv ≫ (pre (δ ▷ A)).app X).app (Opposite.op ⦋1⦌) e.edge
  rw [ihomUncurry_precomp]

/-- 全パラメータの右 Kan 普遍性から、定値族の標準制限 Hom の全単射を回収する。 -/
lemma constantHom_precomp_bijective_of_parameterRightKan {K L X : SSet.{u}}
    [Quasicategory X] (δ : K ⟶ L) (H : L ⟶ X)
    (h : ∀ (A : SSet.{u}) [Quasicategory A], _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal
      (F := uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : A ⟶ (ihom L).obj X))
      (F₀ := (δ ▷ A) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : A ⟶ (ihom L).obj X))
      (δ ▷ A) (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        ((δ ▷ A) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : A ⟶ (ihom L).obj X))))))
    (A : SSet.{u}) [Quasicategory A] (T : L ⟶ X) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.constantHomPostcomp ((pre δ).app X) A
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) := by
  let U : A ⟶ (ihom L).obj X := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T)
  let V : A ⟶ (ihom L).obj X := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)
  let q := (pre δ).app X
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_bijective (K := L) (A := A) (X := X) U V
  have ht := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_bijective (K := K) (A := A) (X := X) (U ≫ q) (V ≫ q)
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (uncurry_pre_app X U δ) (uncurry_pre_app X V δ)
  have ht' := E.bijective.comp ht
  have hb := h A (uncurry U)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanHomMap (F := uncurry V) (F₀ := (δ ▷ A) ≫ uncurry V) (δ ▷ A)
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((δ ▷ A) ≫ uncurry V)))) (uncurry U) =
      ((hoFunctor.map ((pre (δ ▷ A)).app X)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (uncurry U) (uncurry V) →
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((δ ▷ A) ≫ uncurry U) ((δ ▷ A) ≫ uncurry V)) := by
    funext α
    exact Category.comp_id _
  rw [he] at hb
  have hm : Function.Bijective
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ q) (V ≫ q)) := by
    constructor
    · intro α β heq
      apply hs.injective
      apply hb.injective
      rw [← functorHomUncurry_precomp δ α, ← functorHomUncurry_precomp δ β, heq]
    · intro β
      obtain ⟨αu, hαu⟩ := hb.surjective (E (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := X)
        (U := U ≫ q) (V := V ≫ q) β))
      obtain ⟨α', rfl⟩ := hs.surjective αu
      refine ⟨α', ht'.injective ?_⟩
      change E (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry _) = E (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry β)
      dsimp only [E]
      rw [functorHomUncurry_precomp]
      exact hαu
  exact (Iso.homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex T) q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) q)).bijective.comp hm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
