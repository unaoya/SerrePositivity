module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyCompositionOver

/-! # 指定部分と底三角形を同時に保つ相対ホモトピー合成

概要：任意の単射で指定した部分の三角形と、像の底三角形を同時に保持して合成する。
方針：内部 Hom の Leibniz pullback の inner fibration に内二ホーンを持ち上げる。
規約：三角形全体を厳密に保持する。使われ方：実 Ore 三角形族の境界固定の高次貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 指定部分の三角形と、底の三角形全体を同時に厳密に保って合成する。 -/
lemma homotopyCompositionRelativeOver_exists {L K E B : SSet.{u}} (i : L ⟶ K) [Mono i]
    (p : E ⟶ B) [InnerFibration p] {U V W : K ⟶ E}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (DA : (Δ[2] : SSet.{u}) ⟶ (ihom L).obj E)
    (DB : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj B)
    (h₀A : stdSimplex.δ (0 : Fin 3) ≫ DA = curry r.h ≫ (pre i).app E)
    (h₂A : stdSimplex.δ (2 : Fin 3) ≫ DA = curry l.h ≫ (pre i).app E)
    (h₀B : stdSimplex.δ (0 : Fin 3) ≫ DB = curry r.h ≫ (ihom K).map p)
    (h₂B : stdSimplex.δ (2 : Fin 3) ≫ DB = curry l.h ≫ (ihom K).map p)
    (hc : DA ≫ (ihom L).map p = DB ≫ (pre i).app B) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ (pre i).app E = DA ∧ T.diagram ≫ (ihom K).map p = DB := by
  let sq : internalHom.PullbackObjObj i p :=
    Functor.PullbackObjObj.ofHasPullback internalHom i p
  have : InnerFibration sq.π := innerFibration_pullbackObjObjπ sq
  let D := sq.isPullback.lift DA DB hc
  have hDA : D ≫ sq.fst = DA := sq.isPullback.lift_fst _ _ _
  have hDB : D ≫ sq.snd = DB := sq.isPullback.lift_snd _ _ _
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ D = curry r.h ≫ sq.π := by
    apply sq.hom_ext
    · simpa only [Category.assoc, hDA, sq.π_fst] using! h₀A
    · simpa only [Category.assoc, hDB, sq.π_snd] using! h₀B
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ D = curry l.h ≫ sq.π := by
    apply sq.hom_ext
    · simpa only [Category.assoc, hDA, sq.π_fst] using! h₂A
    · simpa only [Category.assoc, hDB, sq.π_snd] using! h₂B
  obtain ⟨d, T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.homotopyCompositionWithImage_exists sq.π l r D h₀ h₂
  have hTA := congrArg (fun k => k ≫ sq.fst) hT
  have hTB := congrArg (fun k => k ≫ sq.snd) hT
  simp only [Category.assoc, sq.π_fst, hDA] at hTA
  simp only [Category.assoc, sq.π_snd, hDB] at hTB
  exact ⟨d, T, hTA, hTB⟩
/-- 底で定値な前比較を、指定部分の全三角形を保って、後比較と同じ底の合成へ移す。 -/
lemma homotopyCompositionRelativeOver_fixedLeft_exists {L K E B : SSet.{u}}
    (i : L ⟶ K) [Mono i] (p : E ⟶ B) [InnerFibration p] {U V W : K ⟶ E}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (hl : l.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ V ≫ p)
    (DA : (Δ[2] : SSet.{u}) ⟶ (ihom L).obj E)
    (h₀A : stdSimplex.δ (0 : Fin 3) ≫ DA = curry r.h ≫ (pre i).app E)
    (h₂A : stdSimplex.δ (2 : Fin 3) ≫ DA = curry l.h ≫ (pre i).app E)
    (hc : DA ≫ (ihom L).map p =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p) ≫ (pre i).app B) :
    ∃ d : SSet.Homotopy U W, ∃ T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      T.diagram ≫ (pre i).app E = DA ∧
      T.diagram ≫ (ihom K).map p =
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p) ∧
      d.h ≫ p = r.h ≫ p := by
  let DB := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r p)
  have h₀B : stdSimplex.δ (0 : Fin 3) ≫ DB = curry r.h ≫ (ihom K).map p := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_zero]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_natural_right, uncurry_curry]
    rfl
  have h₂B : stdSimplex.δ (2 : Fin 3) ≫ DB = curry l.h ≫ (ihom K).map p := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_two]
    apply uncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, uncurry_natural_right, uncurry_curry]
    exact hl.symm
  obtain ⟨d, T, hA, hB⟩ := homotopyCompositionRelativeOver_exists i p l r DA DB
    h₀A h₂A h₀B h₂B hc
  refine ⟨d, T, hA, hB, ?_⟩
  have he := congrArg (fun k => stdSimplex.δ (1 : Fin 3) ≫ k) hB
  rw [← Category.assoc, T.face_one, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_one] at he
  have hu := congrArg uncurry he
  rw [uncurry_natural_right, uncurry_curry, uncurry_curry] at hu
  exact hu

end SerrePositivity.InfinityCategories.Project.DerivedCategories
