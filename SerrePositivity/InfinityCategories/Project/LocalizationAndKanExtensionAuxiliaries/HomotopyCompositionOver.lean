module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofRelativeCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 指定底三角形を保つ実ホモトピー合成

概要：inner fibration 上の二つの実ホモトピーを、像の指定三角形全体を保って合成する。
方針：パラメータ付き内部 Hom の inner fibration に内二ホーンを持ち上げる。
規約：両入力と底の三角形を選び直さない。使われ方：実 Ore 比較の共通対角への貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 任意の inner fibration への像の指定三角形を保ち、指定二ホモトピーを合成する。 -/
lemma homotopyCompositionWithImage_exists {K E Z : SSet.{u}}
    (q : (ihom K).obj E ⟶ Z) [InnerFibration q]
    {U V W : K ⟶ E} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (D : (Δ[2] : SSet.{u}) ⟶ Z)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h ≫ q)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h ≫ q) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ q = D := by
  let Y := (ihom K).obj E
  let e₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l
  let e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r
  let fs : ∀ (j : Fin 3) (_ : j ≠ 1), (Δ[1] : SSet.{u}) ⟶ Y :=
    fun j _ => if j = 0 then SSet.yonedaEquiv.symm e₁.edge else SSet.yonedaEquiv.symm e₀.edge
  have hf : horn.IsCompatible fs := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k
    all_goals try norm_num at hj
    all_goals try norm_num at hk
    all_goals try norm_num at hjk
    change stdSimplex.δ (1 : Fin 2) ≫ (SSet.yonedaEquiv (X := Y)).symm e₁.edge =
      stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv (X := Y)).symm e₀.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
    have hs : Y.δ 1 e₁.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V := e₁.src_eq
    have ht : Y.δ 0 e₀.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V := e₀.tgt_eq
    exact congrArg (SSet.yonedaEquiv (X := Y)).symm (hs.trans ht.symm)
  have hw : hf.desc ≫ q = (horn 2 1).ι ≫ D := by
    apply horn.hom_ext'
    intro j hj
    rw [← Category.assoc, horn.IsCompatible.ι_desc, horn.ι_ι_assoc]
    fin_cases j
    · change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.h)) ≫ _ = _
      rw [Equiv.symm_apply_apply]
      exact h₀.symm
    · exact (hj rfl).elim
    · change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry l.h)) ≫ _ = _
      rw [Equiv.symm_apply_apply]
      exact h₂.symm
  have : HasLiftingProperty (horn 2 (1 : Fin 3)).ι (q) :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))
  let sq : CommSq hf.desc (horn 2 (1 : Fin 3)).ι (q) D := ⟨hw⟩
  have hs₀ : stdSimplex.δ (0 : Fin 3) ≫ sq.lift = curry r.h := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) 0 (by decide), sq.fac_left, horn.IsCompatible.ι_desc]
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.h)) = _
    exact Equiv.symm_apply_apply _ _
  have hs₂ : stdSimplex.δ (2 : Fin 3) ≫ sq.lift = curry l.h := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) 2 (by decide), sq.fac_left, horn.IsCompatible.ι_desc]
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry l.h)) = _
    exact Equiv.symm_apply_apply _ _
  obtain ⟨d, T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.roofCompositionTriangle_of_outerFaces l r sq.lift hs₀ hs₂
  refine ⟨d, T, ?_⟩
  rw [hT]
  exact sq.fac_right

/-- 指定二辺を、その像の指定三角形全体を厳密に保って合成する。 -/
lemma homotopyCompositionOver_exists {K E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    {U V W : K ⟶ E} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (D : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj B)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h ≫ (ihom K).map p)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h ≫ (ihom K).map p) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ (ihom K).map p = D :=
  homotopyCompositionWithImage_exists ((ihom K).map p) l r D h₀ h₂

/-- 前の比較が底で定値なら、同じ後比較の底を保った合成と像の退化三角形を供給する。 -/
lemma homotopyCompositionOver_fixedLeft_exists {K E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] {U V W : K ⟶ E}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (hl : l.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ V ≫ p) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ (ihom K).map p =
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p) ∧
      d.h ≫ p = r.h ≫ p := by
  let D := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p)
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h ≫ (ihom K).map p := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_zero]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_natural_right, uncurry_curry]
    rfl
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h ≫ (ihom K).map p := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_two]
    apply uncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, uncurry_natural_right, uncurry_curry]
    exact hl.symm
  obtain ⟨d, T, hT⟩ := homotopyCompositionOver_exists p l r D h₀ h₂
  refine ⟨d, T, hT, ?_⟩
  have he := congrArg (fun k => stdSimplex.δ (1 : Fin 3) ≫ k) hT
  rw [← Category.assoc, T.face_one, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_one] at he
  have hu := congrArg uncurry he
  rw [uncurry_natural_right, uncurry_curry, uncurry_curry] at hu
  exact hu
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
