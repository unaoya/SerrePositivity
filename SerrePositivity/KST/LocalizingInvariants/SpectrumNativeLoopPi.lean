module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumLoopBoundaryIso

/-!
概要：元の native loop 関手による整数 π の次数移動を、関手の自然同型として供給する。
方針：全 loop 図式の接続同型を元の厳密な終点切断へ引き戻す。
規約：元の nativeLoop と π 関手を使用し、円 cotensor の公開比較との可換性も保持する。
使われ方：K-B K-7 d2 の loop と整数 π の自然な次数移動。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

def nativeLoopPiIso (j : ℤ) :
    (hoFunctor.map nativeLoop.{u}).toFunctor ⋙ piFunctor j ≅ piFunctor (j + 1) := by
  let U := (hoFunctor.map nativeLoopTargetEquivalence.{u}.inv).toFunctor
  let E₀ := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)).toFunctor
  let E₁ := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)).toFunctor
  have h₀ : U ⋙ E₀ = (hoFunctor.map nativeLoop.{u}).toFunctor := by
    change (hoFunctor.map nativeLoopTargetEquivalence.inv ≫
      hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)).toFunctor = _
    rw [← Functor.map_comp]
    rfl
  have h₁ : U ⋙ E₁ = 𝟭 (hoFunctor.obj Sp.{u}) := by
    change (hoFunctor.map nativeLoopTargetEquivalence.inv ≫
      hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)).toFunctor = _
    rw [← Functor.map_comp, nativeLoopTargetEquivalence_inv_target, CategoryTheory.Functor.map_id]
    rfl
  exact (eqToIso (congrArg (fun F => F ⋙ piFunctor j) h₀)).symm ≪≫
    Functor.associator U E₀ (piFunctor j) ≪≫
      Functor.isoWhiskerLeft U (SpectrumLoop.piShiftIso j) ≪≫
        (Functor.associator U E₁ (piFunctor (j + 1))).symm ≪≫
          eqToIso (congrArg (fun F => F ⋙ piFunctor (j + 1)) h₁) ≪≫
            Functor.leftUnitor (piFunctor (j + 1))

def nativeCirclePiIso (j : ℤ) :
    (hoFunctor.map (nativeCotensor PointedSimplicialSet.circle.{u})).toFunctor ⋙
      piFunctor j ≅ piFunctor (j + 1) :=
  Functor.isoWhiskerRight nativeLoopCircleFunctorIso.toNatIso (piFunctor j) ≪≫ nativeLoopPiIso j

lemma nativeLoopPiIso_circle_comparison (j : ℤ) :
    Functor.isoWhiskerRight nativeLoopCircleFunctorIso.{u}.toNatIso (piFunctor j) ≪≫
      nativeLoopPiIso j = nativeCirclePiIso j := rfl

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
