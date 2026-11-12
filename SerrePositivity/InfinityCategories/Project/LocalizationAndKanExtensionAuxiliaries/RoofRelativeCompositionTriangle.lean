module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofCompositionFaces
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-! # 動く境界で指定した合成三角形の相対持ち上げ

概要：二つの実輸送を、部分図式上に指定した実合成二単体と厳密に一致させて合成する。
方針：二辺を内二ホーンに貼り、前合成の内部ファイブレーションに対して持ち上げる。
規約：境界を時間に定値とは仮定しない。使われ方：実屋根比較の二段階輸送の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 任意の指定境界合成三角形を保って、全体の二つの実ホモトピーを合成できる。 -/
lemma roofRelativeCompositionTriangle_exists {L K X : SSet.{u}} [Quasicategory X]
    (i : L ⟶ K) [Mono i] {U V W : K ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (D : (Δ[2] : SSet.{u}) ⟶ (ihom L).obj X)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h ≫ (pre i).app X)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h ≫ (pre i).app X) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ (pre i).app X = D := by
  let Y := (ihom K).obj X
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
  have hw : hf.desc ≫ (pre i).app X = (horn 2 1).ι ≫ D := by
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
  have : HasLiftingProperty (horn 2 (1 : Fin 3)).ι ((pre i).app X) :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))
  let sq : CommSq hf.desc (horn 2 (1 : Fin 3)).ι ((pre i).app X) D := ⟨hw⟩
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

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
