module

public import SerrePositivity.InfinityCategories.F1B.KanCoconeHomLeg
public import SerrePositivity.InfinityCategories.F1B.KanLeftIdentityLeg
public import SerrePositivity.InfinityCategories.F1B.KanLeftTransportComponents
public import SerrePositivity.InfinityCategories.F1B.KanPointColimitLeg
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：充満忠実な inner 包含に沿う左 Kan 拡張の指定単位は可逆。
方針：像の点の恒等終対象で余極限余錐の脚を評価し、局所輸送の自然性で単位へ移す。
規約：指定された自然変換そのものの h Fun の類の可逆性。
使われ方：全部分圏上の元の図式を厳密に保つ Kan 拡張の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：像の点の輸送後の局所余錐が余極限なら、指定単位の対応する成分は可逆。
方針：恒等終対象で二本の脚を可逆とし、固定された頂点成分と自然性で単位を評価する。
規約：任意に選んだ局所輸送 t をそのまま用いる。
使われ方：点ごとの左 Kan 条件から指定単位の可逆性を導く。 -/
lemma kanLeftTransport_identity_unit_component_isIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (k : K _⦋0⦌) (t : LeftKanCoconeTransport δ F₀ F β (δ.app (Opposite.op ⦋0⦌) k))
    (ht : IsColimitCone t.cocone) :
    IsIso (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) k) := by
  let a := kanLeftKanIdentityVertex δ k
  let L := leftKanShape δ (δ.app (Opposite.op ⦋0⦌) k)
  let α := SSet.Truncated.HomotopyCategory.homMk t.edge
  have hc := kanColimit_terminal_leg_invertible t.cocone ht a
    (kanLeftKanIdentityVertex_isTerminal δ hδ k)
  have hd := kanLeftCanonical_identity_leg_invertible δ F k
  have ha : IsIso (functorHomEvaluate α (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u})))) := by
    have := kanLeftTransport_apex_isIso t
    unfold functorHomEvaluate
    change IsIso (eqToHom _ ≫
      (hoFunctor.map (coconeApexEvaluation L D)).toFunctor.map α ≫ eqToHom _)
    infer_instance
  have hs := kanCoconeHom_source_component_isIso t.cocone
    (leftKanCanonicalCocone δ F (δ.app (Opposite.op ⦋0⦌) k)) α
    (SSet.yonedaEquiv.symm a) hc hd ha
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hs
  have hu := (kanLeftTransport_source_component_isIso_iff t a).1 hs
  dsimp only [a] at hu
  rw [kanLeftKanIdentityVertex_projection] at hu
  exact hu

/-- 概要：充満忠実な inner 包含に沿う左 Kan 拡張の単位は各点で可逆。
方針：指定点の像で局所輸送と余極限性を取り出し、恒等終対象の評価を適用する。
規約：元の指定変換 β を変更しない。
使われ方：単位を関手圏全体の同型とするための各点の入力。 -/
lemma kanLeftKanExtension_unit_component_isIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsLeftKanExtension δ F₀ F β) (k : K _⦋0⦌) :
    IsIso (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) k) := by
  obtain ⟨t, ht⟩ := hβ (δ.app (Opposite.op ⦋0⦌) k)
  exact kanLeftTransport_identity_unit_component_isIso δ hδ k t ht

/-- 概要：充満忠実な inner 包含に沿う左 Kan 拡張の指定単位は h Fun で同型。
方針：各点の成分の可逆性を関手圏の辺の点ごとの判定へ渡す。
規約：単に値の点ごとの同型を選ぶのではなく β の同じ類の可逆性。
使われ方：元の図式を保つ Kan 拡張の厳密化。 -/
lemma kanLeftKanExtension_unit_isIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsLeftKanExtension δ F₀ F β) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) := by
  change IsInvertibleEdge (functorEdgeOfSimplicialHomotopy β)
  apply (isInvertibleEdge_iff_evaluateFunctorAt (functorEdgeOfSimplicialHomotopy β)).2
  intro k
  exact (kanFunctorHomEvaluate_isIso_iff _ k).1
    (kanLeftKanExtension_unit_component_isIso δ hδ β hβ k)

end SerrePositivity.InfinityCategories.F1B
