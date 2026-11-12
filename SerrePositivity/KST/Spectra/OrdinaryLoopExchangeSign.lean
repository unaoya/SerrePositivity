module

public import SerrePositivity.KST.Spectra.DeloopedExchangeSign
public import SerrePositivity.KST.Spectra.LoopExchangeOperators

/-!
概要：通常の円の loop を標的とする二重 Kan loop でも、交換と反転の成分作用が一致する。
方針：通常の loop 自身の恒等 Ω 条件に、既存の交換符号定理を適用する。
規約：標的は任意の Kan 複体。使われ方：元の随伴に直接自然な混合三重円の普遍交換区間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra

/-- 内側を通常の円とする loop 値でも、外側二つの Kan 円の交換符号が成り立つ。 -/
lemma ordinaryLoop_exchange_sign (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (LoopExchangePaths.swap
      (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)).right =
    mapπ₀ (LoopExchangePaths.reversal
      (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)).right := by
  let loopKan : KanComplex
      (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact omega_exchange_sign (𝟙 (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _)

end SerrePositivity.KST.Spectra
